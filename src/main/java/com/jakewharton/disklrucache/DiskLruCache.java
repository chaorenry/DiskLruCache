/*
 * Copyright (C) 2011 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.jakewharton.disklrucache;

import java.io.BufferedWriter;
import java.io.Closeable;
import java.io.EOFException;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FilterOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.Callable;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A cache that uses a bounded amount of space on a filesystem. Each cache
 * entry has a string key and a fixed number of values. Each key must match
 * the regex <strong>[a-z0-9_-]{1,120}</strong>. Values are byte sequences,
 * accessible as streams or files. Each value must be between {@code 0} and
 * {@code Integer.MAX_VALUE} bytes in length.
 *
 * <p>The cache stores its data in a directory on the filesystem. This
 * directory must be exclusive to the cache; the cache may delete or overwrite
 * files from its directory. It is an error for multiple processes to use the
 * same cache directory at the same time.
 *
 * <p>This cache limits the number of bytes that it will store on the
 * filesystem. When the number of stored bytes exceeds the limit, the cache will
 * remove entries in the background until the limit is satisfied. The limit is
 * not strict: the cache may temporarily exceed it while waiting for files to be
 * deleted. The limit does not include filesystem overhead or the cache
 * journal so space-sensitive applications should set a conservative limit.
 *
 * <p>Clients call {@link #edit} to create or update the values of an entry. An
 * entry may have only one editor at one time; if a value is not available to be
 * edited then {@link #edit} will return null.
 * <ul>
 * <li>When an entry is being <strong>created</strong> it is necessary to
 * supply a full set of values; the empty value should be used as a
 * placeholder if necessary.
 * <li>When an entry is being <strong>edited</strong>, it is not necessary
 * to supply data for every value; values default to their previous
 * value.
 * </ul>
 * Every {@link #edit} call must be matched by a call to {@link Editor#commit}
 * or {@link Editor#abort}. Committing is atomic: a read observes the full set
 * of values as they were before or after the commit, but never a mix of values.
 *
 * <p>Clients call {@link #get} to read a snapshot of an entry. The read will
 * observe the value at the time that {@link #get} was called. Updates and
 * removals after the call do not impact ongoing reads.
 *
 * <p>This class is tolerant of some I/O errors. If files are missing from the
 * filesystem, the corresponding entries will be dropped from the cache. If
 * an error occurs while writing a cache value, the edit will fail silently.
 * Callers should handle other problems by catching {@code IOException} and
 * responding appropriately.
 */
//继承Closeable以保证可以关闭
public final class DiskLruCache implements Closeable {
  //常量日志文件
  static final String JOURNAL_FILE = "journal";
  static final String JOURNAL_FILE_TEMP = "journal.tmp";
  static final String JOURNAL_FILE_BACKUP = "journal.bkp";
  static final String MAGIC = "libcore.io.DiskLruCache";
  static final String VERSION_1 = "1";
  //序列数量
  static final long ANY_SEQUENCE_NUMBER = -1;
  //key筛选表达式
  static final String STRING_KEY_PATTERN = "[a-z0-9_-]{1,120}";
  static final Pattern LEGAL_KEY_PATTERN = Pattern.compile(STRING_KEY_PATTERN);
  private static final String CLEAN = "CLEAN";
  private static final String DIRTY = "DIRTY";
  private static final String REMOVE = "REMOVE";
  private static final String READ = "READ";

    /*
     * This cache uses a journal file named "journal". A typical journal file
     * looks like this:
     *     libcore.io.DiskLruCache
     *     1
     *     100
     *     2
     *
     *     CLEAN 3400330d1dfc7f3f7f4b8d4d803dfcf6 832 21054
     *     DIRTY 335c4c6028171cfddfbaae1a9c313c52
     *     CLEAN 335c4c6028171cfddfbaae1a9c313c52 3934 2342
     *     REMOVE 335c4c6028171cfddfbaae1a9c313c52
     *     DIRTY 1ab96a171faeeee38496d8b330771a7a
     *     CLEAN 1ab96a171faeeee38496d8b330771a7a 1600 234
     *     READ 335c4c6028171cfddfbaae1a9c313c52
     *     READ 3400330d1dfc7f3f7f4b8d4d803dfcf6
     *
     * The first five lines of the journal form its header. They are the
     * constant string "libcore.io.DiskLruCache", the disk cache's version,
     * the application's version, the value count, and a blank line.
     *
     * Each of the subsequent lines in the file is a record of the state of a
     * cache entry. Each line contains space-separated values: a state, a key,
     * and optional state-specific values.
     *   o DIRTY lines track that an entry is actively being created or updated.
     *     Every successful DIRTY action should be followed by a CLEAN or REMOVE
     *     action. DIRTY lines without a matching CLEAN or REMOVE indicate that
     *     temporary files may need to be deleted.
     *   o CLEAN lines track a cache entry that has been successfully published
     *     and may be read. A publish line is followed by the lengths of each of
     *     its values.
     *   o READ lines track accesses for LRU.
     *   o REMOVE lines track entries that have been deleted.
     *
     * The journal file is appended to as cache operations occur. The journal may
     * occasionally be compacted by dropping redundant lines. A temporary file named
     * "journal.tmp" will be used during compaction; that file should be deleted if
     * it exists when the cache is opened.
     */

  private final File directory;
  private final File journalFile;
  private final File journalFileTmp;
  private final File journalFileBackup;
  //版本号，如果升级版本就会抛弃所有缓存，可以用来远程控制强制刷新缓存
  private final int appVersion;
  private long maxSize;
  private final int valueCount;
  private long size = 0;
  //写日志的基类
  private Writer journalWriter;
  //缓存实体的linkedHashMap
  private final LinkedHashMap<String, Entry> lruEntries =
      new LinkedHashMap<String, Entry>(0, 0.75f, true);

  private int redundantOpCount;

  /**
   * To differentiate between old and current snapshots, each entry is given
   * a sequence number each time an edit is committed. A snapshot is stale if
   * its sequence number is not equal to its entry's sequence number.
   */
  //下一条目序列号，会被直接使用
  private long nextSequenceNumber = 0;

  /** This cache uses a single background thread to evict entries. */
  //一个独立线程池单个后台线程，使用阻塞队列
  final ThreadPoolExecutor executorService =
      new ThreadPoolExecutor(0, 1, 60L, TimeUnit.SECONDS, new LinkedBlockingQueue<Runnable>());
  //完全清理
  private final Callable<Void> cleanupCallable = new Callable<Void>() {
    public Void call() throws Exception {
      //锁DiskLruCache
      synchronized (DiskLruCache.this) {
        if (journalWriter == null) {
          return null; // Closed.
        }
        //移除超出的实体，不符合规则的话会递归调用
        trimToSize();
        //是否需要重建日志
        if (journalRebuildRequired()) {
          //重建日志文件
          rebuildJournal();
          //操作数重置为0
          redundantOpCount = 0;
        }
      }
      return null;
    }
  };
//私有的构造方法，文件存储目录，app版本，每个实体可用版本，最大数据容量
  private DiskLruCache(File directory, int appVersion, int valueCount, long maxSize) {
    this.directory = directory;
    this.appVersion = appVersion;
    this.journalFile = new File(directory, JOURNAL_FILE);
    this.journalFileTmp = new File(directory, JOURNAL_FILE_TEMP);
    this.journalFileBackup = new File(directory, JOURNAL_FILE_BACKUP);
    this.valueCount = valueCount;
    this.maxSize = maxSize;
  }

  /**
   * Opens the cache in {@code directory}, creating a cache if none exists
   * there.
   *
   * @param directory a writable directory
   * @param valueCount the number of values per cache entry. Must be positive.
   * @param maxSize the maximum number of bytes this cache should use to store
   * @throws IOException if reading or writing the cache directory fails
   */
  public static DiskLruCache open(File directory, int appVersion, int valueCount, long maxSize)
      throws IOException {
    if (maxSize <= 0) {
      throw new IllegalArgumentException("maxSize <= 0");
    }
    if (valueCount <= 0) {
      throw new IllegalArgumentException("valueCount <= 0");
    }

    // If a bkp file exists, use it instead.
    File backupFile = new File(directory, JOURNAL_FILE_BACKUP);
    //如果备份日志存在
    if (backupFile.exists()) {
      File journalFile = new File(directory, JOURNAL_FILE);
      // If journal file also exists just delete backup file.
      if (journalFile.exists()) {
        //如果正式日志存在，就删掉备份
        backupFile.delete();
      } else {
        //否则就把备份放入备份版文件
        renameTo(backupFile, journalFile, false);
      }
    }

    // Prefer to pick up where we left off.
    DiskLruCache cache = new DiskLruCache(directory, appVersion, valueCount, maxSize);
    if (cache.journalFile.exists()) {
      try {
        //读取并规整日志
        cache.readJournal();
        //清理脏实体
        cache.processJournal();
        return cache;
      } catch (IOException journalIsCorrupt) {
        System.out
            .println("DiskLruCache "
                + directory
                + " is corrupt: "
                + journalIsCorrupt.getMessage()
                + ", removing");
        cache.delete();
      }
    }

    // Create a new empty cache.
    //如果出错误了，创建缓存空间
    directory.mkdirs();
    cache = new DiskLruCache(directory, appVersion, valueCount, maxSize);
    cache.rebuildJournal();
    return cache;
  }
  //读取日志文件
  private void readJournal() throws IOException {
    StrictLineReader reader = new StrictLineReader(new FileInputStream(journalFile), Util.US_ASCII);
    //按行核实日志文件内容
    try {
      String magic = reader.readLine();
      String version = reader.readLine();
      String appVersionString = reader.readLine();
      String valueCountString = reader.readLine();
      String blank = reader.readLine();
      if (!MAGIC.equals(magic)
          || !VERSION_1.equals(version)
          || !Integer.toString(appVersion).equals(appVersionString)
          || !Integer.toString(valueCount).equals(valueCountString)
          || !"".equals(blank)) {
        throw new IOException("unexpected journal header: [" + magic + ", " + version + ", "
            + valueCountString + ", " + blank + "]");
      }

      int lineCount = 0;
      while (true) {
        try {
          //按行读取日志，并把对应的缓存文件改成相应的状态
          readJournalLine(reader.readLine());
          lineCount++;
        } catch (EOFException endOfJournal) {
          break;
        }
      }
      //重新对齐操作数
      redundantOpCount = lineCount - lruEntries.size();

      // If we ended on a truncated line, rebuild the journal before appending to it.
      //如果我们以截断行作为结束，那么要在追加日志之前先重建日志

      if (reader.hasUnterminatedLine()) {
        //如果有未正确结束的行，重建日志
        rebuildJournal();
      } else {
        //之前的日志正确结束，可以建立写入了
        journalWriter = new BufferedWriter(new OutputStreamWriter(
            new FileOutputStream(journalFile, true), Util.US_ASCII));
      }
    } finally {
      //最终结束读线程
      Util.closeQuietly(reader);
    }
  }

  private void readJournalLine(String line) throws IOException {
    //操作日志的每行开头有个空格
    int firstSpace = line.indexOf(' ');
    if (firstSpace == -1) {
      throw new IOException("unexpected journal line: " + line);
    }

    int keyBegin = firstSpace + 1;
    //寻找结束空格的位置
    int secondSpace = line.indexOf(' ', keyBegin);
    final String key;
    if (secondSpace == -1) {
      //如果没有结束空格
      //从line中截取KEY
      key = line.substring(keyBegin);
      if (firstSpace == REMOVE.length() && line.startsWith(REMOVE)) {
        //如果这行的操作是REMOVE ,那就真的从实体集合中将改实体移除，然后返回
        lruEntries.remove(key);
        return;
      }
    } else {
      key = line.substring(keyBegin, secondSpace);
    }
    //否则,确保集合中有这个实体
    Entry entry = lruEntries.get(key);
    if (entry == null) {
      entry = new Entry(key);
      lruEntries.put(key, entry);
    }
    //如果是cleanup行
    if (secondSpace != -1 && firstSpace == CLEAN.length() && line.startsWith(CLEAN)) {
      //截取行后内容
      String[] parts = line.substring(secondSpace + 1).split(" ");
      entry.readable = true;
      entry.currentEditor = null;
      entry.setLengths(parts);
    } else if (secondSpace == -1 && firstSpace == DIRTY.length() && line.startsWith(DIRTY)) {
      entry.currentEditor = new Editor(entry);
    } else if (secondSpace == -1 && firstSpace == READ.length() && line.startsWith(READ)) {
      // This work was already done by calling lruEntries.get().
    } else {
      throw new IOException("unexpected journal line: " + line);
    }
  }

  /**
   * Computes the initial size and collects garbage as a part of opening the
   * cache. Dirty entries are assumed to be inconsistent and will be deleted.
   */

  //计算初始大小并收集垃圾作为打开缓存的一部分。假设脏条目不一致，将被删除。
  private void processJournal() throws IOException {
    //删掉临时日志
    deleteIfExists(journalFileTmp);
    //遍历缓存实体
    for (Iterator<Entry> i = lruEntries.values().iterator(); i.hasNext(); ) {

      Entry entry = i.next();

      if (entry.currentEditor == null) {
        //如果该实体为垃圾状态，将实体的大小也计算进入总大小
        for (int t = 0; t < valueCount; t++) {
          size += entry.lengths[t];
        }
      } else {
        //如果该实体为编辑状态
        entry.currentEditor = null;
        //todo???
        for (int t = 0; t < valueCount; t++) {
          deleteIfExists(entry.getCleanFile(t));
          deleteIfExists(entry.getDirtyFile(t));
        }
        i.remove();
      }
    }
  }

  /**
   * Creates a new journal that omits redundant information. This replaces the
   * current journal if it exists.
   */
  private synchronized void rebuildJournal() throws IOException {
    //关闭输出流
    if (journalWriter != null) {
      journalWriter.close();
    }
    //新建一个临时文件，创建写入
    Writer writer = new BufferedWriter(
        new OutputStreamWriter(new FileOutputStream(journalFileTmp), Util.US_ASCII));
    try {
      writer.write(MAGIC);
      writer.write("\n");
      writer.write(VERSION_1);
      writer.write("\n");
      writer.write(Integer.toString(appVersion));
      writer.write("\n");
      writer.write(Integer.toString(valueCount));
      writer.write("\n");
      writer.write("\n");

      for (Entry entry : lruEntries.values()) {
        if (entry.currentEditor != null) {
          //当前实体 正在写入 ，记录实体KEY
          writer.write(DIRTY + ' ' + entry.key + '\n');
        } else {
          //当前实体 没在写入，记录当前实体长度
          writer.write(CLEAN + ' ' + entry.key + entry.getLengths() + '\n');
        }
      }
    } finally {
      //最后，关闭写入
      writer.close();
    }
    //如果原来的日志文件存再
    if (journalFile.exists()) {
      //把原来的日志文件移动到备份位置，并重命名为备份文件
      renameTo(journalFile, journalFileBackup, true);
    }
    //再把新生成的临时文件，重命名为正式的日志文件
    renameTo(journalFileTmp, journalFile, false);
    //都完成之后，删除备份文件
    journalFileBackup.delete();
    //准备好正式日志文件的写入
    journalWriter = new BufferedWriter(
        new OutputStreamWriter(new FileOutputStream(journalFile, true), Util.US_ASCII));
  }

  private static void deleteIfExists(File file) throws IOException {
    if (file.exists() && !file.delete()) {
      throw new IOException();
    }
  }
  //移动并重命名
  private static void renameTo(File from, File to, boolean deleteDestination) throws IOException {
    if (deleteDestination) {
      deleteIfExists(to);
    }
    if (!from.renameTo(to)) {
      throw new IOException();
    }
  }

  /**
   * Returns a snapshot of the entry named {@code key}, or null if it doesn't
   * exist is not currently readable. If a value is returned, it is moved to
   * the head of the LRU queue.
   */
  /**
   *返回名为{@code key}的条目的快照，如果不存在，则返回null当前不可读。如果返回值，则将其移动到LRU队列的头部。
   * @param key
   * @return
   * @throws IOException
   */
  public synchronized Snapshot get(String key) throws IOException {
    //检查缓存是否已关闭
    checkNotClosed();
    //验证KEY命名规则
    validateKey(key);
    Entry entry = lruEntries.get(key);
    if (entry == null) {
      return null;
    }

    if (!entry.readable) {
      return null;
    }

    // Open all streams eagerly to guarantee that we see a single published
    // snapshot. If we opened streams lazily then the streams could come
    // from different edits.
    //尽快的打开流，以保证不会被其他线程的写操作改变最新版本
    InputStream[] ins = new InputStream[valueCount];
    try {
      for (int i = 0; i < valueCount; i++) {
        ins[i] = new FileInputStream(entry.getCleanFile(i));
      }
    } catch (FileNotFoundException e) {
      // A file must have been deleted manually!
      //文件流必须被手动关闭
      for (int i = 0; i < valueCount; i++) {
        if (ins[i] != null) {
          Util.closeQuietly(ins[i]);
        } else {
          break;
        }
      }
      return null;
    }
    //追加操作数
    redundantOpCount++;
    //追加操作日志
    journalWriter.append(READ + ' ' + key + '\n');
    if (journalRebuildRequired()) {
      executorService.submit(cleanupCallable);
    }

    return new Snapshot(key, entry.sequenceNumber, ins, entry.lengths);
  }

  /**
   * Returns an editor for the entry named {@code key}, or null if another
   * edit is in progress.
   */
  public Editor edit(String key) throws IOException {
    return edit(key, ANY_SEQUENCE_NUMBER);
  }

  private synchronized Editor edit(String key, long expectedSequenceNumber //预期的序列号
  ) throws IOException {
    //检查未关闭
    checkNotClosed();
    validateKey(key);
    Entry entry = lruEntries.get(key);
    if (expectedSequenceNumber != ANY_SEQUENCE_NUMBER && (entry == null
        || entry.sequenceNumber != expectedSequenceNumber)) {
      //期望序列号不违法，但是装载实体为空或者期望序列号不违法，但装载实体最后一个序列号不是期望序列号
      return null; // Snapshot is stale.
    }

    if (entry == null) {
      //如果装载实体为空，且期望序列号违法，填充进去
      entry = new Entry(key);
      lruEntries.put(key, entry);
    } else if (entry.currentEditor != null) {
      //如果已经有其他editor
      return null; // Another edit is in progress.
    }

    Editor editor = new Editor(entry);
    entry.currentEditor = editor;

    // Flush the journal before creating files to prevent file leaks.
    //在创建文件之前刷新日志以防止文件泄漏。
    journalWriter.write(DIRTY + ' ' + key + '\n');
    journalWriter.flush();
    return editor;
  }

  /** Returns the directory where this cache stores its data. */
  public File getDirectory() {
    return directory;
  }

  /**
   * Returns the maximum number of bytes that this cache should use to store
   * its data.
   */
  public synchronized long getMaxSize() {
    return maxSize;
  }

  /**
   * Changes the maximum number of bytes the cache can store and queues a job
   * to trim the existing store, if necessary.
   */
  public synchronized void setMaxSize(long maxSize) {
    this.maxSize = maxSize;
    executorService.submit(cleanupCallable);
  }

  /**
   * Returns the number of bytes currently being used to store the values in
   * this cache. This may be greater than the max size if a background
   * deletion is pending.
   */
  public synchronized long size() {
    return size;
  }

  private synchronized void completeEdit(Editor editor, boolean success) throws IOException {
    Entry entry = editor.entry;
    if (entry.currentEditor != editor) {
      throw new IllegalStateException();
    }

    // If this edit is creating the entry for the first time, every index must have a value.
    if (success && !entry.readable) {
      for (int i = 0; i < valueCount; i++) {
        if (!editor.written[i]) {
          editor.abort();
          throw new IllegalStateException("Newly created entry didn't create value for index " + i);
        }
        if (!entry.getDirtyFile(i).exists()) {
          editor.abort();
          return;
        }
      }
    }

    for (int i = 0; i < valueCount; i++) {
      File dirty = entry.getDirtyFile(i);
      if (success) {
        if (dirty.exists()) {
          File clean = entry.getCleanFile(i);
          dirty.renameTo(clean);
          long oldLength = entry.lengths[i];
          long newLength = clean.length();
          entry.lengths[i] = newLength;
          size = size - oldLength + newLength;
        }
      } else {
        deleteIfExists(dirty);
      }
    }

    redundantOpCount++;
    entry.currentEditor = null;
    if (entry.readable | success) {
      entry.readable = true;
      journalWriter.write(CLEAN + ' ' + entry.key + entry.getLengths() + '\n');
      if (success) {
        entry.sequenceNumber = nextSequenceNumber++;
      }
    } else {
      lruEntries.remove(entry.key);
      journalWriter.write(REMOVE + ' ' + entry.key + '\n');
    }
    journalWriter.flush();

    if (size > maxSize || journalRebuildRequired()) {
      executorService.submit(cleanupCallable);
    }
  }

  /**
   * We only rebuild the journal when it will halve the size of the journal
   * and eliminate at least 2000 ops.
   */
  //操作大于2000次 且 添加删除操作数大于实体数量，需要重建
  private boolean journalRebuildRequired() {
    final int redundantOpCompactThreshold = 2000;
    return redundantOpCount >= redundantOpCompactThreshold //
        && redundantOpCount >= lruEntries.size();
  }

  /**
   * Drops the entry for {@code key} if it exists and can be removed. Entries
   * actively being edited cannot be removed.
   *
   * @return true if an entry was removed.
   */
  //如果实体存在并且可移除，就drop掉。无法删除正在编辑的条目。
  public synchronized boolean remove(String key) throws IOException {
    //DiskLruCache如果没被关闭，并且KEY命名符合要求
    checkNotClosed();
    validateKey(key);
    //获取实体
    Entry entry = lruEntries.get(key);
    //如果不是在编辑
    if (entry == null || entry.currentEditor != null) {
      return false;
    }
    //遍历该KEY 所有数量的缓存，并统统删除
    for (int i = 0; i < valueCount; i++) {
      //通过名称拼接获取最开始的缓存文件
      File file = entry.getCleanFile(i);
      //如果文件存在，且未被删除
      if (file.exists() && !file.delete()) {
        throw new IOException("failed to delete " + file);
      }
      //从总大小中减去该文件大小
      size -= entry.lengths[i];
      //将刚才的文件大小标记为零
      entry.lengths[i] = 0;
    }

    //冗余操作数加1
    redundantOpCount++;
    //在日志文件中记录该次操作
    journalWriter.append(REMOVE + ' ' + key + '\n');
    //实体map中彻底移除该key
    lruEntries.remove(key);
    //如果需要重建日志，那么线程池提交清理，并重建日志文件
    if (journalRebuildRequired()) {
      executorService.submit(cleanupCallable);
    }

    return true;
  }

  /** Returns true if this cache has been closed. */
  public synchronized boolean isClosed() {
    return journalWriter == null;
  }
  //可写性如果是空，就意味着已经被关闭
  private void checkNotClosed() {
    if (journalWriter == null) {
      throw new IllegalStateException("cache is closed");
    }
  }

  /** Force buffered operations to the filesystem. */
  public synchronized void flush() throws IOException {
    checkNotClosed();
    trimToSize();
    journalWriter.flush();
  }

  /** Closes this cache. Stored values will remain on the filesystem. */
  public synchronized void close() throws IOException {
    if (journalWriter == null) {
      return; // Already closed.
    }
    for (Entry entry : new ArrayList<Entry>(lruEntries.values())) {
      if (entry.currentEditor != null) {
        entry.currentEditor.abort();
      }
    }
    trimToSize();
    journalWriter.close();
    journalWriter = null;
  }
//从实体存储中移除最后一个
  private void trimToSize() throws IOException {
    while (size > maxSize) {
      Map.Entry<String, Entry> toEvict = lruEntries.entrySet().iterator().next();
      remove(toEvict.getKey());
    }
  }

  /**
   * Closes the cache and deletes all of its stored values. This will delete
   * all files in the cache directory including files that weren't created by
   * the cache.
   */
  public void delete() throws IOException {
    close();
    Util.deleteContents(directory);
  }
  //验证一下KEY 是否符合名称的正则要求
  private void validateKey(String key) {
    Matcher matcher = LEGAL_KEY_PATTERN.matcher(key);
    if (!matcher.matches()) {
      throw new IllegalArgumentException("keys must match regex "
              + STRING_KEY_PATTERN + ": \"" + key + "\"");
    }
  }

  private static String inputStreamToString(InputStream in) throws IOException {
    return Util.readFully(new InputStreamReader(in, Util.UTF_8));
  }

  /** A snapshot of the values for an entry. */
  //将缓存实体转换为一个实例，每个版本的实体都是一个inputsteam
  public final class Snapshot implements Closeable {
    private final String key;
    private final long sequenceNumber;
    private final InputStream[] ins;
    private final long[] lengths;

    private Snapshot(String key, long sequenceNumber, InputStream[] ins, long[] lengths) {
      this.key = key;
      this.sequenceNumber = sequenceNumber;
      this.ins = ins;
      this.lengths = lengths;
    }

    /**
     * Returns an editor for this snapshot's entry, or null if either the
     * entry has changed since this snapshot was created or if another edit
     * is in progress.
     */
    public Editor edit() throws IOException {
      return DiskLruCache.this.edit(key, sequenceNumber);
    }

    /** Returns the unbuffered stream with the value for {@code index}. */
    public InputStream getInputStream(int index) {
      return ins[index];
    }

    /** Returns the string value for {@code index}. */
    public String getString(int index) throws IOException {
      return inputStreamToString(getInputStream(index));
    }

    /** Returns the byte length of the value for {@code index}. */
    public long getLength(int index) {
      return lengths[index];
    }

    public void close() {
      for (InputStream in : ins) {
        Util.closeQuietly(in);
      }
    }
  }

  private static final OutputStream NULL_OUTPUT_STREAM = new OutputStream() {
    @Override
    public void write(int b) throws IOException {
      // Eat all writes silently. Nom nom.
    }
  };

  /** Edits the values for an entry. */
  public final class Editor {
    private final Entry entry;
    private final boolean[] written;
    private boolean hasErrors;
    private boolean committed;

    private Editor(Entry entry) {
      this.entry = entry;
      this.written = (entry.readable) ? null : new boolean[valueCount];
    }

    /**
     * Returns an unbuffered input stream to read the last committed value,
     * or null if no value has been committed.
     */
    public InputStream newInputStream(int index) throws IOException {
      synchronized (DiskLruCache.this) {
        if (entry.currentEditor != this) {
          throw new IllegalStateException();
        }
        if (!entry.readable) {
          return null;
        }
        try {
          return new FileInputStream(entry.getCleanFile(index));
        } catch (FileNotFoundException e) {
          return null;
        }
      }
    }

    /**
     * Returns the last committed value as a string, or null if no value
     * has been committed.
     */
    public String getString(int index) throws IOException {
      InputStream in = newInputStream(index);
      return in != null ? inputStreamToString(in) : null;
    }

    /**
     * Returns a new unbuffered output stream to write the value at
     * {@code index}. If the underlying output stream encounters errors
     * when writing to the filesystem, this edit will be aborted when
     * {@link #commit} is called. The returned output stream does not throw
     * IOExceptions.
     */
    public OutputStream newOutputStream(int index) throws IOException {
      if (index < 0 || index >= valueCount) {
        throw new IllegalArgumentException("Expected index " + index + " to "
                + "be greater than 0 and less than the maximum value count "
                + "of " + valueCount);
      }
      synchronized (DiskLruCache.this) {
        if (entry.currentEditor != this) {
          throw new IllegalStateException();
        }
        if (!entry.readable) {
          written[index] = true;
        }
        File dirtyFile = entry.getDirtyFile(index);
        FileOutputStream outputStream;
        try {
          outputStream = new FileOutputStream(dirtyFile);
        } catch (FileNotFoundException e) {
          // Attempt to recreate the cache directory.
          directory.mkdirs();
          try {
            outputStream = new FileOutputStream(dirtyFile);
          } catch (FileNotFoundException e2) {
            // We are unable to recover. Silently eat the writes.
            return NULL_OUTPUT_STREAM;
          }
        }
        return new FaultHidingOutputStream(outputStream);
      }
    }

    /** Sets the value at {@code index} to {@code value}. */
    public void set(int index, String value) throws IOException {
      Writer writer = null;
      try {
        writer = new OutputStreamWriter(newOutputStream(index), Util.UTF_8);
        writer.write(value);
      } finally {
        Util.closeQuietly(writer);
      }
    }

    /**
     * Commits this edit so it is visible to readers.  This releases the
     * edit lock so another edit may be started on the same key.
     */
    public void commit() throws IOException {
      if (hasErrors) {
        completeEdit(this, false);
        remove(entry.key); // The previous entry is stale.
      } else {
        completeEdit(this, true);
      }
      committed = true;
    }

    /**
     * Aborts this edit. This releases the edit lock so another edit may be
     * started on the same key.
     */
    public void abort() throws IOException {
      completeEdit(this, false);
    }

    public void abortUnlessCommitted() {
      if (!committed) {
        try {
          abort();
        } catch (IOException ignored) {
        }
      }
    }

    private class FaultHidingOutputStream extends FilterOutputStream {
      private FaultHidingOutputStream(OutputStream out) {
        super(out);
      }

      @Override public void write(int oneByte) {
        try {
          out.write(oneByte);
        } catch (IOException e) {
          hasErrors = true;
        }
      }

      @Override public void write(byte[] buffer, int offset, int length) {
        try {
          out.write(buffer, offset, length);
        } catch (IOException e) {
          hasErrors = true;
        }
      }

      @Override public void close() {
        try {
          out.close();
        } catch (IOException e) {
          hasErrors = true;
        }
      }

      @Override public void flush() {
        try {
          out.flush();
        } catch (IOException e) {
          hasErrors = true;
        }
      }
    }
  }

  private final class Entry {
    private final String key;

    /** Lengths of this entry's files. */
    private final long[] lengths;

    /** True if this entry has ever been published. */
    private boolean readable;

    /** The ongoing edit or null if this entry is not being edited. */
    private Editor currentEditor;

    /** The sequence number of the most recently committed edit to this entry. */
    private long sequenceNumber;

    private Entry(String key) {
      this.key = key;
      this.lengths = new long[valueCount];
    }

    public String getLengths() throws IOException {
      StringBuilder result = new StringBuilder();
      for (long size : lengths) {
        result.append(' ').append(size);
      }
      return result.toString();
    }

    /** Set lengths using decimal numbers like "10123". */
    private void setLengths(String[] strings) throws IOException {
      if (strings.length != valueCount) {
        throw invalidLengths(strings);
      }

      try {
        for (int i = 0; i < strings.length; i++) {
          lengths[i] = Long.parseLong(strings[i]);
        }
      } catch (NumberFormatException e) {
        throw invalidLengths(strings);
      }
    }

    private IOException invalidLengths(String[] strings) throws IOException {
      throw new IOException("unexpected journal line: " + java.util.Arrays.toString(strings));
    }

    public File getCleanFile(int i) {
      return new File(directory, key + "." + i);
    }

    public File getDirtyFile(int i) {
      return new File(directory, key + "." + i + ".tmp");
    }
  }
}
