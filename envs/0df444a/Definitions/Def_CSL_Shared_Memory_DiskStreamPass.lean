-- Prove2me | Definitions.Def_CSL_Shared_Memory_DiskStreamPass
-- name    : CSL_Shared_Memory_DiskStreamPass
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:08:38.585899+00:00
-- url     : https://prove2.me/theorems/0daad78f-6c34-4e10-8bbf-b508160b2458
-- title:
--   Coded sorting library: Shared / Memory / DiskStreamPass
-- statement:
--   Module `CodedSorting.Shared.Memory.DiskStreamPass` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # An online disk-to-disk stream pass
--
--   The implementation reads the source through Reader.pop, dispatches the value
--   to a bucket writer, and later pops bucket readers directly into one persistent
--   output writer. No runtime list of input or output payloads is accumulated.
--   Lists in correctness statements describe external disk contents only.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.DiskStreamPass

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Programs_TagErasure
import Definitions.Def_CSL_Shared_Memory_StreamCopy
import Mathlib.Data.List.Sort

section DiskStreamPass
/-!
# An online disk-to-disk stream pass

The implementation reads the source through Reader.pop, dispatches the value
to a bucket writer, and later pops bucket readers directly into one persistent
output writer. No runtime list of input or output payloads is accumulated.
Lists in correctness statements describe external disk contents only.
-/

set_option autoImplicit false
namespace CSL.DiskStreamPass
open BucketMachine BucketReader TagErasure
variable {Value : Type*} {Q K : ℕ}

/-- Actual source reader and bucket writers. The input payload is obtained
only by pop; the public counter determines its bucket. -/
def distribute (key : Fin Q → Fin K) (B : ℕ) :
    (remaining offset : ℕ) → offset + remaining ≤ Q →
      Reader Value → (Fin K → Writer Value) →
        Option (Reader Value × (Fin K → Writer Value))
  | 0, _, _, source, buckets => some (source,buckets)
  | n+1, offset, bound, source, buckets =>
      match source.pop with
      | none => none
      | some (a,next) => distribute key B n (offset+1) (by omega) next
          (pushValue B (key ⟨offset,by omega⟩) a buckets)

/-- Actual output writer: each bucket payload is pushed immediately. -/
def reconstruct (schedule : Fin Q → Fin K) (B : ℕ) :
    (remaining offset : ℕ) → offset + remaining ≤ Q →
      (Fin K → Reader Value) → Writer Value →
        Option ((Fin K → Reader Value) × Writer Value)
  | 0, _, _, readers, writer => some (readers,writer)
  | n+1, offset, bound, readers, writer =>
      match (readers (schedule ⟨offset,by omega⟩)).pop with
      | none => none
      | some (a,next) => reconstruct schedule B n (offset+1) (by omega)
          (fun k => if k = schedule ⟨offset,by omega⟩ then next else readers k)
          (writer.push B a)

private theorem pushValue_valid (B : ℕ) (k : Fin K) (a : Value)
    (buckets : Fin K → Writer Value) (hv : ∀ j, (buckets j).Valid B) :
    ∀ j, (pushValue B k a buckets j).Valid B := by
  intro j
  unfold pushValue
  split_ifs
  · exact Writer.push_valid B _ a (hv j)
  · exact hv j

/-- Refinement to the earlier indexed specification. F is used only here,
never by the implementation. The source reader's actual refill conservation
law is carried through the whole scan. -/
theorem distribute_refines (key : Fin Q → Fin K) (F : Fin Q → Value) (B : ℕ)
    (n offset : ℕ) (bound : offset+n ≤ Q)
    (source : Reader Value) (buckets : Fin K → Writer Value) (tail : List Value)
    (hs : source.Valid B) (hb : ∀ k, (buckets k).Valid B)
    (hc : source.contents = (indices n offset bound).map F ++ tail) :
    ∃ finalSource,
      distribute key B n offset bound source buckets =
        some (finalSource,writeIndexed key F B n offset bound buckets) ∧
      finalSource.Valid B ∧ finalSource.contents = tail ∧
      finalSource.reads + finalSource.disk.length = source.reads + source.disk.length ∧
      ∀ k, (writeIndexed key F B n offset bound buckets k).Valid B := by
  induction n generalizing offset source buckets with
  | zero =>
    exact ⟨source,rfl,hs,by simpa using hc,rfl,hb⟩
  | succ n ih =>
    let x : Fin Q := ⟨offset,by omega⟩
    have hc' : source.contents = F x :: ((indices n (offset+1) (by omega)).map F ++ tail) := by
      simpa only [indices_succ,List.map_cons,List.cons_append] using hc
    obtain ⟨next,hpop⟩ := Reader.pop_exists B source hs (F x) _ hc'
    have hn : next.contents = (indices n (offset+1) (by omega)).map F ++ tail := by
      have hh := Reader.pop_contents source next (F x) hpop
      rw [hc'] at hh
      exact (List.cons.inj hh).2.symm
    obtain ⟨final,hfinal,hv,ht,hcount,hbfinal⟩ := ih (offset+1) (by omega) next
      (pushValue B (key x) (F x) buckets) (Reader.pop_valid B _ _ _ hs hpop)
      (pushValue_valid B _ _ _ hb) hn
    refine ⟨final,?_,hv,ht,?_,hbfinal⟩
    · simpa only [distribute,hpop,writeIndexed] using hfinal
    · exact hcount.trans (Reader.pop_conservation _ _ _ hpop)

/-- Equality to the semantic reader, with its returned list used only as a
proof witness for the effect of the online writer. -/
theorem reconstruct_refines (schedule : Fin Q → Fin K) (B : ℕ)
    (n offset : ℕ) (bound : offset+n ≤ Q)
    (readers : Fin K → Reader Value) (writer : Writer Value) :
    reconstruct schedule B n offset bound readers writer =
      (readIndexed schedule n offset bound readers).map
        (fun result => (result.2,result.1.foldl (Writer.push B) writer)) := by
  induction n generalizing offset readers writer with
  | zero => rfl
  | succ n ih =>
    simp only [reconstruct,readIndexed]
    cases hp : (readers (schedule ⟨offset,by omega⟩)).pop with
    | none => rfl
    | some pair =>
      obtain ⟨a,next⟩ := pair
      simp only
      rw [ih]
      cases readIndexed schedule n (offset+1) (by omega)
        (fun k => if k = schedule ⟨offset,by omega⟩ then next else readers k) <;> rfl

private theorem foldWriter_valid (B : ℕ) (xs : List Value) (writer : Writer Value)
    (hw : writer.Valid B) : (xs.foldl (Writer.push B) writer).Valid B := by
  induction xs generalizing writer with
  | nil => exact hw
  | cons a rest ih => exact ih _ (Writer.push_valid B _ _ hw)

private theorem foldWriter_contents (B : ℕ) (xs : List Value) (writer : Writer Value) :
    (xs.foldl (Writer.push B) writer).contents = writer.contents ++ xs := by
  induction xs generalizing writer with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons,ih,Writer.push_contents]
    simp only [List.append_assoc,List.singleton_append]

private theorem pack_full_prefix (B : ℕ) (hB : 0 < B) (front back : List Value)
    (hfront : front.length = B) : pack B hB (front ++ back) = front :: pack B hB back := by
  cases front with
  | nil => simp only [List.length_nil] at hfront; omega
  | cons a rest =>
    rw [List.cons_append,pack]
    change (a :: rest ++ back).take B :: pack B hB ((a :: rest ++ back).drop B) = _
    rw [List.take_left' hfront,List.drop_left' hfront]

private theorem pack_canonical (B : ℕ) (hB : 0 < B)
    (blocks : List (List Value)) (pending : List Value)
    (hblocks : ∀ block ∈ blocks, block.length = B) (hp : pending.length < B) :
    pack B hB (blocks.flatten ++ pending) =
      if pending.isEmpty then blocks else blocks ++ [pending] := by
  induction blocks with
  | nil =>
    cases pending with
    | nil => simp [pack]
    | cons a rest =>
      simp only [List.flatten_nil,List.nil_append,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte]
      rw [pack,List.take_of_length_le (Nat.le_of_lt hp),
        List.drop_eq_nil_of_le (Nat.le_of_lt hp)]
      rw [pack]
  | cons block rest ih =>
    rw [List.flatten_cons,List.append_assoc,
      pack_full_prefix B hB block _ (hblocks block (by simp)),
      ih (fun b hb => hblocks b (by simp [hb]))]
    split_ifs <;> rfl

/-- A flushed online writer has exactly the canonical physical blocking.
Hence composing passes never requires a free repack or a hidden copy. -/
theorem writer_finish_eq_pack (B : ℕ) (hB : 0 < B) (writer : Writer Value)
    (hw : writer.Valid B) : writer.finish = pack B hB writer.contents := by
  exact (pack_canonical B hB writer.blocks writer.pending hw.1 hw.2).symm

/-- Distribution preserves its source and bucket-buffer bounds after every
successful prefix, including prefixes before the source has been exhausted. -/
theorem distribute_valid (key : Fin Q → Fin K) (B : ℕ)
    (n offset : ℕ) (bound : offset+n ≤ Q)
    (source finalSource : Reader Value) (buckets finalBuckets : Fin K → Writer Value)
    (hs : source.Valid B) (hb : ∀ k, (buckets k).Valid B)
    (hdone : distribute key B n offset bound source buckets = some (finalSource,finalBuckets)) :
    finalSource.Valid B ∧ ∀ k, (finalBuckets k).Valid B := by
  induction n generalizing offset source buckets with
  | zero =>
    obtain ⟨rfl,rfl⟩ := (Prod.mk.inj (Option.some.inj hdone))
    exact ⟨hs,hb⟩
  | succ n ih =>
    cases hp : source.pop with
    | none => simp [distribute,hp] at hdone
    | some pair =>
      obtain ⟨a,next⟩ := pair
      simp only [distribute,hp] at hdone
      exact ih (offset+1) (by omega) next _ (Reader.pop_valid B _ _ _ hs hp)
        (pushValue_valid B _ _ _ hb) hdone

/-- Reconstruction preserves bucket reader and output writer bounds after
every prefix. The output is external blocks plus one bounded pending block. -/
theorem reconstruct_valid (schedule : Fin Q → Fin K) (B : ℕ)
    (n offset : ℕ) (bound : offset+n ≤ Q)
    (readers finalReaders : Fin K → Reader Value) (writer finalWriter : Writer Value)
    (hr : ∀ k, (readers k).Valid B) (hw : writer.Valid B)
    (hdone : reconstruct schedule B n offset bound readers writer = some (finalReaders,finalWriter)) :
    (∀ k, (finalReaders k).Valid B) ∧ finalWriter.Valid B := by
  induction n generalizing offset readers writer with
  | zero =>
    obtain ⟨rfl,rfl⟩ := (Prod.mk.inj (Option.some.inj hdone))
    exact ⟨hr,hw⟩
  | succ n ih =>
    cases hp : (readers (schedule ⟨offset,by omega⟩)).pop with
    | none => simp [reconstruct,hp] at hdone
    | some pair =>
      obtain ⟨a,next⟩ := pair
      simp only [reconstruct,hp] at hdone
      apply ih (offset+1) (by omega) _ (writer.push B a) _ (Writer.push_valid B _ _ hw) hdone
      intro k
      split_ifs with hk
      · subst k
        exact Reader.pop_valid B _ _ _ (hr _) hp
      · exact hr k

private theorem writer_memory (B : ℕ) (buckets : Fin K → Writer Value)
    (hb : ∀ k, (buckets k).Valid B) : writerOccupancy buckets ≤ K * B := by
  have h := reader_memory B (fun k => (⟨[],(buckets k).pending,0⟩ : Reader Value))
    (fun k => ⟨by simp, (hb k).2⟩)
  exact h

theorem distribute_prefix_memory (key : Fin Q → Fin K) (B : ℕ)
    (n offset : ℕ) (bound : offset+n ≤ Q)
    (source finalSource : Reader Value) (buckets finalBuckets : Fin K → Writer Value)
    (hs : source.Valid B) (hb : ∀ k, (buckets k).Valid B)
    (hdone : distribute key B n offset bound source buckets = some (finalSource,finalBuckets)) :
    finalSource.pending.length + writerOccupancy finalBuckets ≤ (K+2)*B := by
  obtain ⟨hsource,hbuckets⟩ := distribute_valid key B n offset bound source finalSource
    buckets finalBuckets hs hb hdone
  have hm := writer_memory B finalBuckets hbuckets
  have hr := hsource.2
  rw [Nat.add_mul]
  omega

theorem reconstruct_prefix_memory (schedule : Fin Q → Fin K) (B : ℕ)
    (n offset : ℕ) (bound : offset+n ≤ Q)
    (readers finalReaders : Fin K → Reader Value) (writer finalWriter : Writer Value)
    (hr : ∀ k, (readers k).Valid B) (hw : writer.Valid B)
    (hdone : reconstruct schedule B n offset bound readers writer = some (finalReaders,finalWriter)) :
    occupiedReaders finalReaders + finalWriter.pending.length ≤ (K+2)*B := by
  obtain ⟨hreaders,hwriter⟩ := reconstruct_valid schedule B n offset bound readers finalReaders
    writer finalWriter hr hw hdone
  have hm := reader_memory B finalReaders hreaders
  have hw := hwriter.2
  rw [Nat.add_mul]
  omega

/-- These counters are summaries of actual refills and writer flushes. The
completed output blocks are external storage, not an in-memory payload list. -/
structure PassResult (K : ℕ) (Value : Type*) where
  sourceReads : ℕ
  bucketWrites : ℕ
  readers : Fin K → Reader Value
  output : Writer Value

def PassResult.transfers (result : PassResult K Value) : ℕ :=
  result.sourceReads + result.bucketWrites + readCount result.readers + result.output.finish.length

/-- End-to-end implementation. F and the target payload list do not occur
in this definition. The only input is the already-existing source disk. -/
def run (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K) (B : ℕ)
    (sourceBlocks : List (List Value)) : Option (PassResult K Value) := do
  let (source,buckets) ← distribute key B Q 0 (by omega)
    (Reader.fromDisk sourceBlocks) (fun _ => Writer.empty)
  let sourceReads := source.reads
  let bucketWrites := ((List.finRange K).map (fun k => (buckets k).finish.length)).sum
  -- Finish transfers every pending bucket block to disk before reader buffers
  -- are allocated. Only the two control counts survive the phase boundary.
  let (readers,output) ← reconstruct (fun y => key (e.symm y)) B Q 0 (by omega)
    (fun k => Reader.fromDisk (buckets k).finish) Writer.empty
  return ⟨sourceReads,bucketWrites,readers,output⟩

/-- The online machine refines the indexed semantic loops and counts all
source reads and output writes as real state transitions. This version
accepts any valid source blocking, so completed output disks can be chained. -/
theorem run_refines (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (F : Fin Q → Value) (B : ℕ) (hB : 0 < B)
    (sourceBlocks : List (List Value))
    (hs : (Reader.fromDisk sourceBlocks).Valid B)
    (hc : sourceBlocks.flatten = inputValues F)
    (final : Fin K → Reader Value)
    (hread : readIndexed (fun y => key (e.symm y)) Q 0 (by omega)
      (valueReaders key F B) = some (outputValues e F,final)) :
    ∃ result,
      run e key B sourceBlocks = some result ∧
      result.output.finish.flatten = outputValues e F ∧
      result.output.Valid B ∧ (∀ k, (result.readers k).Valid B) ∧
      result.sourceReads = sourceBlocks.length ∧
      result.bucketWrites = valueFlushCount key F B ∧ result.readers = final ∧
      result.output.finish.length = (pack B hB (outputValues e F)).length ∧
      result.transfers + (pack B hB (inputValues F)).length =
        valueTransfers e key F B hB final + sourceBlocks.length := by
  have hcontent : (Reader.fromDisk sourceBlocks).contents =
      (indices Q 0 (by omega)).map F ++ [] := by
    simpa only [Reader.contents,Reader.fromDisk,List.nil_append,indices_full,
      List.append_nil,inputValues] using hc
  obtain ⟨source,hdistribution,hsource,hempty,hcount,hbuckets⟩ :=
    distribute_refines key F B Q 0 (by omega) (Reader.fromDisk sourceBlocks)
      (fun _ => Writer.empty) [] hs (fun _ => Writer.empty_valid B hB) hcontent
  have hsourceCount : source.reads = sourceBlocks.length := by
    have hd := Reader.empty_contents_disk B source hsource hempty
    simpa only [hd,List.length_nil,Nat.add_zero,Reader.fromDisk,Nat.zero_add] using hcount
  let writer := (outputValues e F).foldl (Writer.push B) Writer.empty
  have hwriter : writer.Valid B := foldWriter_valid B _ _ (Writer.empty_valid B hB)
  have hwcontents : writer.contents = outputValues e F := by
    simpa only [writer,Writer.empty,Writer.contents,List.flatten_nil,List.nil_append] using
      foldWriter_contents B (outputValues e F) Writer.empty
  have hwcount : writer.finish.length = (pack B hB (outputValues e F)).length := by
    rw [Writer.finish_count B _ hwriter,hwcontents,pack_count]
  have hreconstruct : reconstruct (fun y => key (e.symm y)) B Q 0 (by omega)
      (valueReaders key F B) Writer.empty = some (final,writer) := by
    rw [reconstruct_refines,hread]
    rfl
  let result : PassResult K Value := ⟨source.reads,valueFlushCount key F B,final,writer⟩
  refine ⟨result,?_,?_,hwriter,?_,hsourceCount,rfl,rfl,hwcount,?_⟩
  · unfold run
    rw [hdistribution]
    change (reconstruct (fun y => key (e.symm y)) B Q 0 (by omega)
      (valueReaders key F B) Writer.empty).bind _ = _
    rw [hreconstruct]
    rfl
  · exact (Writer.finish_contents writer).trans hwcontents
  · exact readIndexed_valid _ B Q 0 (by omega) (valueReaders key F B)
      (valueReaders_valid key F B hB) _ final hread
  · change source.reads + valueFlushCount key F B + readCount final + writer.finish.length + _ = _
    rw [hsourceCount,hwcount]
    unfold valueTransfers
    omega

/-- Complete physical pass theorem, with the same concrete transfer bound
as the earlier semantic specification. The source need only have the same
number of blocks as a packed stream, not definitionally be that pack. -/
theorem run_correct (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (hinc : ∀ x y, x < y → key x = key y → e x < e y)
    (F : Fin Q → Value) (B : ℕ) (hB : 0 < B)
    (sourceBlocks : List (List Value))
    (hs : (Reader.fromDisk sourceBlocks).Valid B)
    (hc : sourceBlocks.flatten = inputValues F)
    (hn : sourceBlocks.length = (pack B hB (inputValues F)).length) :
    ∃ result,
      run e key B sourceBlocks = some result ∧
      result.output.finish.flatten = outputValues e F ∧
      result.transfers ≤ 4 * (Q / B) + 2 * K + 2 ∧
      result.output.Valid B ∧ (∀ k, (result.readers k).Valid B) ∧
      result.output.finish.length = (pack B hB (outputValues e F)).length := by
  obtain ⟨final,hread,hcost,_⟩ := increasing_value_reconstruction e key hinc F B hB
  obtain ⟨result,hrun,hout,hwriter,hreaders,_,_,_,houtput,hcount⟩ :=
    run_refines e key F B hB sourceBlocks hs hc final hread
  refine ⟨result,hrun,hout,?_,hwriter,hreaders,houtput⟩
  rw [hn] at hcount
  omega

theorem run_packed (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (hinc : ∀ x y, x < y → key x = key y → e x < e y)
    (F : Fin Q → Value) (B : ℕ) (hB : 0 < B) :
    ∃ result,
      run e key B (pack B hB (inputValues F)) = some result ∧
      result.output.finish.flatten = outputValues e F ∧
      result.transfers ≤ 4 * (Q / B) + 2 * K + 2 ∧
      result.output.Valid B ∧ (∀ k, (result.readers k).Valid B) ∧
      result.output.finish.length = (pack B hB (outputValues e F)).length :=
  run_correct e key hinc F B hB _ (StreamCopy.pack_reader_valid B hB _)
    (flatten_pack B hB _) rfl

/-- The real completed output disk is already the packed target file,
with equality of blocks, not only equality after flattening. -/
theorem run_packed_canonical (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (hinc : ∀ x y, x < y → key x = key y → e x < e y)
    (F : Fin Q → Value) (B : ℕ) (hB : 0 < B) :
    ∃ result,
      run e key B (pack B hB (inputValues F)) = some result ∧
      result.output.finish = pack B hB (outputValues e F) ∧
      result.transfers ≤ 4 * (Q / B) + 2 * K + 2 ∧
      result.output.Valid B ∧ (∀ k, (result.readers k).Valid B) := by
  obtain ⟨result,hrun,hout,hcost,hw,hr,_⟩ := run_packed e key hinc F B hB
  refine ⟨result,hrun,?_,hcost,hw,hr⟩
  rw [Writer.finish_contents] at hout
  rw [writer_finish_eq_pack B hB result.output hw,hout]

end CSL.DiskStreamPass
end DiskStreamPass

section PhysicalFilePartition
/-! Splitting and concatenation of external files. The source reader persists across split boundaries, and the output writer persists across join boundaries. Each operation reads and writes the current disk file. 


-/
namespace CSL.PhysicalFilePartition
open BucketMachine BucketReader StreamCopy
variable {α : Type*}

/-- Strengthen the split specification from flattened contents to the exact
canonical blocks consumed by the physical network interpreter. -/
theorem split_canonical (B : ℕ) (hB : 0 < B) (pieces : List (List α))
    (reader : Reader α) (hr : reader.Valid B) (hc : reader.contents=pieces.flatten) :
    ∃ finalReader,
      splitFiles B (pieces.map List.length) reader =
        some (pieces.map (pack B hB),finalReader) ∧
      finalReader.Valid B ∧ finalReader.contents=[] ∧
      finalReader.reads=reader.reads+reader.disk.length := by
  induction pieces generalizing reader with
  | nil =>
    have hd := Reader.empty_contents_disk B reader hr hc
    exact ⟨reader,rfl,hr,hc,by simp [hd]⟩
  | cons p rest ih =>
    obtain ⟨t,ht,hv,hs,hw,hn⟩ := copy_prefix B p rest.flatten
      ⟨reader,Writer.empty⟩ ⟨hr,Writer.empty_valid B hB⟩ hc
    have hcontents : t.target.contents=p := by
      simpa [Writer.empty,Writer.contents] using hw
    have hfile : t.target.finish=pack B hB p := by
      rw [DiskStreamPass.writer_finish_eq_pack B hB _ hv.2,hcontents]
    obtain ⟨last,hl,hlv,hlc,hlr⟩ := ih t.source hv.1 hs
    refine ⟨last,?_,hlv,hlc,?_⟩
    · simp only [List.map_cons,splitFiles,ht,hl,hfile]
    · exact hlr.trans hn

structure File (α : Type*) where
  blocks : List (List α)
  records : ℕ

/-- Only the stored count controls the loop; the disk payload is accessed
through `Reader.pop` inside `StreamCopy.run`. -/
def join (B : ℕ) : List (File α) → Writer α → Option (Writer α × ℕ)
  | [],writer => some (writer,0)
  | file::rest,writer => do
      let copied ← run B file.records ⟨Reader.fromDisk file.blocks,writer⟩
      let tail ← join B rest copied.target
      return (tail.1,copied.source.reads+tail.2)

def descriptors (B : ℕ) (hB : 0 < B) (pieces : List (List α)) : List (File α) :=
  pieces.map (fun p => ⟨pack B hB p,p.length⟩)

theorem join_canonical (B : ℕ) (hB : 0 < B) (pieces : List (List α))
    (writer : Writer α) (hw : writer.Valid B) :
    ∃ finalWriter,
      join B (descriptors B hB pieces) writer =
        some (finalWriter,(pieces.map (fun p => (pack B hB p).length)).sum) ∧
      finalWriter.Valid B ∧ finalWriter.contents=writer.contents++pieces.flatten := by
  induction pieces generalizing writer with
  | nil => exact ⟨writer,rfl,hw,by simp⟩
  | cons p rest ih =>
    obtain ⟨t,ht,hv,hs,hc,hn⟩ := copy_prefix B p []
      ⟨Reader.fromDisk (pack B hB p),writer⟩
      ⟨pack_reader_valid B hB p,hw⟩
      (by simp [Reader.contents,Reader.fromDisk,flatten_pack])
    have hd := Reader.empty_contents_disk B t.source hv.1 hs
    have hreads : t.source.reads=(pack B hB p).length := by
      simpa [hd,Reader.fromDisk] using hn
    obtain ⟨last,hl,hlv,hlc⟩ := ih t.target hv.2
    refine ⟨last,?_,hlv,?_⟩
    · simp only [descriptors] at hl
      simp [descriptors,join,ht,hl,hreads]
    · rw [hlc,hc]
      simp only [List.flatten_cons,List.append_assoc]

/-- The returned count includes every source refill and the final flush.
The runtime does not compute a file's length by scanning its contents. -/
def gather (B : ℕ) (files : List (File α)) : Option (List (List α) × ℕ) := do
  let result ← join B files Writer.empty
  return (result.1.finish,result.2+result.1.finish.length)

theorem gather_canonical (B : ℕ) (hB : 0 < B) (pieces : List (List α)) :
    gather B (descriptors B hB pieces)=some (pack B hB pieces.flatten,
      (pieces.map (fun p => (pack B hB p).length)).sum+
      (pack B hB pieces.flatten).length) := by
  obtain ⟨last,hr,hv,hc⟩ := join_canonical B hB pieces Writer.empty (Writer.empty_valid B hB)
  have hf : last.finish=pack B hB pieces.flatten := by
    rw [DiskStreamPass.writer_finish_eq_pack B hB _ hv,hc]
    simp [Writer.empty,Writer.contents]
  simp [gather,hr,hf]

def scatter (B : ℕ) (lengths : List ℕ) (source : List (List α)) :
    Option (List (List (List α)) × ℕ) := do
  let result ← splitFiles B lengths (Reader.fromDisk source)
  return (result.1,result.2.reads+(result.1.map List.length).sum)

theorem scatter_canonical (B : ℕ) (hB : 0 < B) (pieces : List (List α)) :
    scatter B (pieces.map List.length) (pack B hB pieces.flatten)=
      some (pieces.map (pack B hB),(pack B hB pieces.flatten).length+
        (pieces.map (fun p => (pack B hB p).length)).sum) := by
  obtain ⟨last,hr,_,_,hc⟩ := split_canonical B hB pieces
    (Reader.fromDisk (pack B hB pieces.flatten))
    (pack_reader_valid B hB pieces.flatten)
    (by simp [Reader.contents,Reader.fromDisk,flatten_pack])
  unfold scatter
  rw [hr]
  simp [hc,Reader.fromDisk,List.map_map,Function.comp_def]

def scanCost (B : ℕ) (hB : 0 < B) (pieces : List (List α)) : ℕ :=
  (pack B hB pieces.flatten).length+
    (pieces.map (fun p => (pack B hB p).length)).sum

theorem pieces_cost_bound (B : ℕ) (hB : 0 < B) (pieces : List (List α)) :
    (pieces.map (fun p => (pack B hB p).length)).sum*B ≤
      pieces.flatten.length+pieces.length*B := by
  induction pieces with
  | nil => simp
  | cons p rest ih =>
    have hp := (pack_capacity B hB p).2
    simp only [List.map_cons,List.sum_cons,List.flatten_cons,List.length_append,
      List.length_cons,Nat.add_mul,Nat.succ_mul]
    omega

/-- Both directions incur one complete source/output scan and one scan of
the separately aligned files, including every partial-block boundary. -/
theorem scanCost_bound (B : ℕ) (hB : 0 < B) (pieces : List (List α)) :
    scanCost B hB pieces*B ≤ 2*pieces.flatten.length+(pieces.length+1)*B := by
  have hwhole := (pack_capacity B hB pieces.flatten).2
  have hparts := pieces_cost_bound B hB pieces
  unfold scanCost
  rw [Nat.add_mul,Nat.add_mul]
  omega

/-- With a fixed number of role files, boundary overhead is constant times
one block; the bound does not assume every individual file has a full block. -/
theorem fixed_family_bound {K n : ℕ} (B : ℕ) (hB : 0 < B)
    (values : Fin K → Fin n → α) :
    scanCost B hB (List.ofFn (fun k => List.ofFn (values k)))*B ≤
      2*(K*n)+(K+1)*B := by
  have hlen : (List.ofFn (fun k => List.ofFn (values k))).flatten.length=K*n := by
    rw [List.length_flatten]
    simp [List.map_ofFn,Function.comp_def,List.ofFn_const]
  simpa only [hlen,List.length_ofFn] using
    scanCost_bound B hB (List.ofFn (fun k => List.ofFn (values k)))

end CSL.PhysicalFilePartition
end PhysicalFilePartition

section StreamMask
/-! Padding and erasure are actual online scans. The mask depends only on a
public position counter. Runtime payloads are obtained by Reader.pop and
immediately sent to Writer.push; specification lists are not runtime RAM. -/

set_option autoImplicit false
namespace CSL.StreamMask
open BucketMachine BucketReader StreamCopy
variable {Value : Type*}

def positions (n offset : ℕ) : List ℕ := List.range' offset n

@[simp] theorem positions_zero (offset : ℕ) : positions 0 offset = [] := rfl
@[simp] theorem positions_succ (n offset : ℕ) :
    positions (n+1) offset = offset :: positions n (offset+1) := rfl

def kept (mask : ℕ → Bool) (F : ℕ → Value) (n offset : ℕ) : List Value :=
  ((positions n offset).filter mask).map F

def padded (mask : ℕ → Bool) (padding : Value) (F : ℕ → Value)
    (n offset : ℕ) : List Value :=
  (positions n offset).map (fun x => if mask x then F x else padding)

/-- A false position creates one padding value without reading the source. -/
def insert (mask : ℕ → Bool) (padding : Value) (B : ℕ) :
    ℕ → ℕ → State Value → Option (State Value)
  | 0, _, s => some s
  | n+1, offset, s =>
      if mask offset then
        (step B s).bind (insert mask padding B n (offset+1))
      else insert mask padding B n (offset+1) ⟨s.source,s.target.push B padding⟩

/-- Every position is read, but only valid positions are written. -/
def erase (mask : ℕ → Bool) (B : ℕ) :
    ℕ → ℕ → State Value → Option (State Value)
  | 0, _, s => some s
  | n+1, offset, s =>
      match s.source.pop with
      | none => none
      | some (a,next) => erase mask B n (offset+1)
          ⟨next,if mask offset then s.target.push B a else s.target⟩

theorem insert_correct (mask : ℕ → Bool) (padding : Value) (B n offset : ℕ)
    (F : ℕ → Value) (tail : List Value) (s : State Value)
    (hs : s.Valid B) (hc : s.source.contents = kept mask F n offset ++ tail) :
    ∃ t, insert mask padding B n offset s = some t ∧ t.Valid B ∧
      t.source.contents = tail ∧
      t.target.contents = s.target.contents ++ padded mask padding F n offset ∧
      t.source.reads + t.source.disk.length = s.source.reads + s.source.disk.length := by
  induction n generalizing offset s with
  | zero => exact ⟨s,rfl,hs,by simpa [kept] using hc,by simp [padded],rfl⟩
  | succ n ih =>
    cases hm : mask offset with
    | false =>
      have hc' : s.source.contents = kept mask F n (offset+1) ++ tail := by
        simpa [kept,hm] using hc
      let next : State Value := ⟨s.source,s.target.push B padding⟩
      have hv : next.Valid B := ⟨hs.1,Writer.push_valid B _ _ hs.2⟩
      obtain ⟨t,ht,hv,hsour,htarg,hread⟩ := ih (offset+1) next hv hc'
      refine ⟨t,by simpa [insert,hm,next] using ht,hv,hsour,?_,hread⟩
      rw [htarg]
      simp [next,Writer.push_contents,padded,hm,List.append_assoc]
    | true =>
      have hc' : s.source.contents = F offset :: (kept mask F n (offset+1) ++ tail) := by
        simpa [kept,hm] using hc
      obtain ⟨reader,hpop⟩ := Reader.pop_exists B s.source hs.1 (F offset) _ hc'
      let next : State Value := ⟨reader,s.target.push B (F offset)⟩
      have hstep : step B s = some next := by simp [step,hpop,next]
      have hnext : next.source.contents = kept mask F n (offset+1) ++ tail := by
        have hh := Reader.pop_contents s.source reader (F offset) hpop
        rw [hc'] at hh
        exact (List.cons.inj hh).2.symm
      obtain ⟨t,ht,hv,hsour,htarg,hread⟩ := ih (offset+1) next
        (step_valid B _ _ hs hstep) hnext
      refine ⟨t,by simpa [insert,hm,hstep] using ht,hv,hsour,?_,?_⟩
      · rw [htarg]
        simp [next,Writer.push_contents,padded,hm,List.append_assoc]
      · exact hread.trans (Reader.pop_conservation _ _ _ hpop)

theorem erase_correct (mask : ℕ → Bool) (B n offset : ℕ)
    (F : ℕ → Value) (tail : List Value) (s : State Value)
    (hs : s.Valid B) (hc : s.source.contents = (positions n offset).map F ++ tail) :
    ∃ t, erase mask B n offset s = some t ∧ t.Valid B ∧
      t.source.contents = tail ∧
      t.target.contents = s.target.contents ++ kept mask F n offset ∧
      t.source.reads + t.source.disk.length = s.source.reads + s.source.disk.length := by
  induction n generalizing offset s with
  | zero => exact ⟨s,rfl,hs,by simpa using hc,by simp [kept],rfl⟩
  | succ n ih =>
    have hc' : s.source.contents = F offset :: ((positions n (offset+1)).map F ++ tail) := by
      simpa using hc
    obtain ⟨reader,hpop⟩ := Reader.pop_exists B s.source hs.1 (F offset) _ hc'
    let next : State Value :=
      ⟨reader,if mask offset then s.target.push B (F offset) else s.target⟩
    have hv : next.Valid B := by
      refine ⟨Reader.pop_valid B _ _ _ hs.1 hpop,?_⟩
      try dsimp [next]
      split <;> [exact Writer.push_valid B _ _ hs.2; exact hs.2]
    have hnext : next.source.contents = (positions n (offset+1)).map F ++ tail := by
      have hh := Reader.pop_contents s.source reader (F offset) hpop
      rw [hc'] at hh
      exact (List.cons.inj hh).2.symm
    obtain ⟨t,ht,hv,hsour,htarg,hread⟩ := ih (offset+1) next hv hnext
    refine ⟨t,by simpa [erase,hpop,next] using ht,hv,hsour,?_,
      hread.trans (Reader.pop_conservation _ _ _ hpop)⟩
    rw [htarg]
    cases hm : mask offset <;>
      simp [next,Writer.push_contents,kept,hm,List.append_assoc]

theorem insert_valid (mask : ℕ → Bool) (padding : Value) (B n offset : ℕ)
    (s t : State Value) (hs : s.Valid B)
    (hr : insert mask padding B n offset s = some t) : t.Valid B := by
  induction n generalizing offset s with
  | zero => exact (Option.some.inj hr) ▸ hs
  | succ n ih =>
    cases hm : mask offset with
    | false =>
      simp only [insert,hm,Bool.false_eq_true,↓reduceIte] at hr
      exact ih (offset+1) ⟨s.source,s.target.push B padding⟩
        ⟨hs.1,Writer.push_valid B _ _ hs.2⟩ hr
    | true =>
      simp only [insert,hm,↓reduceIte] at hr
      cases hstep : step B s with
      | none => simp [hstep] at hr
      | some next =>
        simp only [hstep,Option.bind_some] at hr
        exact ih _ _ (step_valid B _ _ hs hstep) hr

theorem erase_valid (mask : ℕ → Bool) (B n offset : ℕ)
    (s t : State Value) (hs : s.Valid B)
    (hr : erase mask B n offset s = some t) : t.Valid B := by
  induction n generalizing offset s with
  | zero => exact (Option.some.inj hr) ▸ hs
  | succ n ih =>
    cases hp : s.source.pop with
    | none => simp [erase,hp] at hr
    | some pair =>
      obtain ⟨a,next⟩ := pair
      simp only [erase,hp] at hr
      apply ih _ _ ?_ hr
      refine ⟨Reader.pop_valid B _ _ _ hs.1 hp,?_⟩
      split <;> [exact Writer.push_valid B _ _ hs.2; exact hs.2]

/-- Includes every prefix: choose any n and its corresponding offset. -/
theorem insert_memory (mask : ℕ → Bool) (padding : Value) (B n offset : ℕ)
    (s t : State Value) (hs : s.Valid B)
    (hr : insert mask padding B n offset s = some t) : t.memory ≤ 2*B :=
  valid_memory B t (insert_valid mask padding B n offset s t hs hr)

theorem erase_memory (mask : ℕ → Bool) (B n offset : ℕ)
    (s t : State Value) (hs : s.Valid B)
    (hr : erase mask B n offset s = some t) : t.memory ≤ 2*B :=
  valid_memory B t (erase_valid mask B n offset s t hs hr)

/-- Accepts the actual input file. No replacement by pack is performed. -/
theorem insert_file (mask : ℕ → Bool) (padding : Value) (B n : ℕ) (hB : 0<B)
    (F : ℕ → Value) (file : List (List Value))
    (hv : (Reader.fromDisk file).Valid B) (hf : file.flatten = kept mask F n 0) :
    ∃ t, insert mask padding B n 0 ⟨Reader.fromDisk file,Writer.empty⟩ = some t ∧
      t.Valid B ∧ t.target.finish = pack B hB (padded mask padding F n 0) ∧
      t.source.reads + t.target.finish.length = file.length + (n+B-1)/B ∧
      t.memory ≤ 2*B := by
  obtain ⟨t,ht,hvalid,hsource,htarget,hreads⟩ := insert_correct mask padding B n 0 F []
    ⟨Reader.fromDisk file,Writer.empty⟩ ⟨hv,Writer.empty_valid B hB⟩
    (by simpa [Reader.contents,Reader.fromDisk] using hf)
  have hcontents : t.target.contents = padded mask padding F n 0 := by
    simpa [Writer.contents,Writer.empty] using htarget
  have hd := Reader.empty_contents_disk B t.source hvalid.1 hsource
  have hr : t.source.reads = file.length := by simpa [hd,Reader.fromDisk] using hreads
  have hw : t.target.finish = pack B hB (padded mask padding F n 0) := by
    rw [DiskStreamPass.writer_finish_eq_pack B hB _ hvalid.2,hcontents]
  refine ⟨t,ht,hvalid,hw,?_,valid_memory B t hvalid⟩
  rw [hr,hw,pack_count]
  simp [padded,positions]

theorem erase_file (mask : ℕ → Bool) (B n : ℕ) (hB : 0<B)
    (F : ℕ → Value) (file : List (List Value))
    (hv : (Reader.fromDisk file).Valid B) (hf : file.flatten = (positions n 0).map F) :
    ∃ t, erase mask B n 0 ⟨Reader.fromDisk file,Writer.empty⟩ = some t ∧
      t.Valid B ∧ t.target.finish = pack B hB (kept mask F n 0) ∧
      t.source.reads + t.target.finish.length =
        file.length + ((kept mask F n 0).length+B-1)/B ∧ t.memory ≤ 2*B := by
  obtain ⟨t,ht,hvalid,hsource,htarget,hreads⟩ := erase_correct mask B n 0 F []
    ⟨Reader.fromDisk file,Writer.empty⟩ ⟨hv,Writer.empty_valid B hB⟩
    (by simpa [Reader.contents,Reader.fromDisk] using hf)
  have hcontents : t.target.contents = kept mask F n 0 := by
    simpa [Writer.contents,Writer.empty] using htarget
  have hd := Reader.empty_contents_disk B t.source hvalid.1 hsource
  have hr : t.source.reads = file.length := by simpa [hd,Reader.fromDisk] using hreads
  have hw : t.target.finish = pack B hB (kept mask F n 0) := by
    rw [DiskStreamPass.writer_finish_eq_pack B hB _ hvalid.2,hcontents]
  exact ⟨t,ht,hvalid,hw,by rw [hr,hw,pack_count],valid_memory B t hvalid⟩

end CSL.StreamMask
end StreamMask


