-- Prove2me | Definitions.Def_CSL_Shared_Memory_StreamCopy
-- name    : CSL_Shared_Memory_StreamCopy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:44:14.392378+00:00
-- url     : https://prove2.me/theorems/030f30da-9c99-47d5-b259-1a7333be65f1
-- title:
--   Coded sorting library: Shared / Memory / StreamCopy
-- statement:
--   Module `CodedSorting.Shared.Memory.StreamCopy` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   A sequential copy machine with one reader block and one writer block.
--   Completed blocks and unread blocks live on disk; only pending buffers count
--   as data memory. The logical lists specify disk contents, not RAM allocation.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.StreamCopy

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Programs_BucketReader

/-! A sequential copy machine with one reader block and one writer block.
Completed blocks and unread blocks live on disk; only pending buffers count
as data memory. The logical lists specify disk contents, not RAM allocation. -/
namespace CSL.StreamCopy
open BucketMachine BucketReader
variable {α : Type*}

structure State (α : Type*) where
  source : Reader α
  target : Writer α

def State.Valid (B : ℕ) (s : State α) := s.source.Valid B ∧ s.target.Valid B

def State.memory (s : State α) := s.source.pending.length + s.target.pending.length

def step (B : ℕ) (s : State α) : Option (State α) :=
  match s.source.pop with
  | none => none
  | some (a, t) => some ⟨t, s.target.push B a⟩

def run (B : ℕ) : ℕ → State α → Option (State α)
  | 0, s => some s
  | n + 1, s => (step B s).bind (run B n)

theorem valid_memory (B : ℕ) (s : State α) (hs : s.Valid B) : s.memory ≤ 2 * B := by
  unfold State.memory
  have hr := hs.1.2
  have hw := hs.2.2
  omega

theorem step_valid (B : ℕ) (s t : State α) (hs : s.Valid B) (ht : step B s = some t) :
    t.Valid B := by
  unfold step at ht
  cases hp : s.source.pop with
  | none => simp [hp] at ht
  | some pair =>
    obtain ⟨a, source⟩ := pair
    simp only [hp, Option.some.injEq] at ht
    subst t
    exact ⟨Reader.pop_valid B _ _ _ hs.1 hp, Writer.push_valid B _ _ hs.2⟩

/-- Every prefix of execution has at most one reader buffer and one writer
buffer. This is an invariant of the actual refill/flush transitions. -/
theorem run_valid (B n : ℕ) (s t : State α) (hs : s.Valid B)
    (ht : run B n s = some t) : t.Valid B := by
  induction n generalizing s with
  | zero =>
    have he : s = t := Option.some.inj ht
    exact he ▸ hs
  | succ n ih =>
    simp only [run] at ht
    cases he : step B s with
    | none => simp [he] at ht
    | some next =>
      simp only [he, Option.bind_some] at ht
      exact ih next (step_valid B s next hs he) ht

theorem run_memory (B n : ℕ) (s t : State α) (hs : s.Valid B)
    (ht : run B n s = some t) : t.memory ≤ 2 * B :=
  valid_memory B t (run_valid B n s t hs ht)

/-- Copy any specified initial segment. Source records are consumed in order,
target records are appended intact, and each source refill is counted once. -/
theorem copy_prefix (B : ℕ) (front back : List α) (s : State α)
    (hs : s.Valid B) (hc : s.source.contents = front ++ back) :
    ∃ t, run B front.length s = some t ∧ t.Valid B ∧
      t.source.contents = back ∧ t.target.contents = s.target.contents ++ front ∧
      t.source.reads + t.source.disk.length = s.source.reads + s.source.disk.length := by
  induction front generalizing s with
  | nil =>
    refine ⟨s, rfl, hs, ?_, ?_, rfl⟩
    · simpa using hc
    · simp
  | cons a rest ih =>
    have hc' : s.source.contents = a :: (rest ++ back) := by simpa using hc
    obtain ⟨nextSource, hp⟩ := Reader.pop_exists B s.source hs.1 a _ hc'
    let next : State α := ⟨nextSource, s.target.push B a⟩
    have hstep : step B s = some next := by simp [step, hp, next]
    have hn := step_valid B s next hs hstep
    have hnc : next.source.contents = rest ++ back := by
      have h := Reader.pop_contents _ _ _ hp
      rw [hc'] at h
      exact List.cons.inj h |>.2.symm
    obtain ⟨t, ht, hv, hsource, htarget, hreads⟩ := ih next hn hnc
    refine ⟨t, ?_, hv, hsource, ?_, ?_⟩
    · simpa only [List.length_cons, run, hstep, Option.bind_some] using ht
    · rw [htarget]
      simp [next, Writer.push_contents, List.append_assoc]
    · have hpcount := Reader.pop_conservation _ _ _ hp
      change t.source.reads + t.source.disk.length = _ at hreads
      exact hreads.trans hpcount

/-- A complete copy writes exactly ceil(n/B) blocks when the initial writer
is empty. The reader can span fragments without resetting its input buffer. -/
theorem copy_stream (B : ℕ) (hB : 0 < B) (xs : List α) (reader : Reader α)
    (hr : reader.Valid B) (hc : reader.contents = xs) :
    ∃ t, run B xs.length ⟨reader, Writer.empty⟩ = some t ∧ t.Valid B ∧
      t.target.finish.flatten = xs ∧
      t.target.finish.length = (xs.length + B - 1) / B ∧
      t.source.reads = reader.reads + reader.disk.length ∧ t.memory ≤ 2 * B := by
  obtain ⟨t, ht, hv, hs, hw, hn⟩ := copy_prefix B xs [] ⟨reader, Writer.empty⟩
    ⟨hr, Writer.empty_valid B hB⟩ (by simpa using hc)
  have hd := Reader.empty_contents_disk B t.source hv.1 hs
  refine ⟨t, ht, hv, ?_, ?_, ?_, valid_memory B t hv⟩
  · rw [Writer.finish_contents, hw]
    simp [Writer.empty, Writer.contents]
  · rw [Writer.finish_count B _ hv.2, hw]
    simp [Writer.empty, Writer.contents]
  · simpa [hd] using hn

/-- Split a single input stream into consecutive, separately block-aligned
files. The lengths are descriptors; only one file writer is active at once. -/
def splitFiles (B : ℕ) : List ℕ → Reader α → Option (List (List (List α)) × Reader α)
  | [], reader => some ([], reader)
  | n :: rest, reader =>
      match run B n ⟨reader, Writer.empty⟩ with
      | none => none
      | some t =>
          match splitFiles B rest t.source with
          | none => none
          | some (files, finalReader) => some (t.target.finish :: files, finalReader)

/-- This theorem counts genuine writer flushes and source refills of the
sequential split operation, including empty intervals and partial blocks. -/
theorem splitFiles_correct (B : ℕ) (hB : 0 < B) (pieces : List (List α))
    (reader : Reader α) (hr : reader.Valid B) (hc : reader.contents = pieces.flatten) :
    ∃ files finalReader,
      splitFiles B (pieces.map List.length) reader = some (files, finalReader) ∧
      files.map List.flatten = pieces ∧
      files.map List.length = pieces.map (fun p => (pack B hB p).length) ∧
      (∀ file ∈ files, (Reader.fromDisk file).Valid B) ∧
      finalReader.Valid B ∧ finalReader.contents = [] ∧
      finalReader.reads = reader.reads + reader.disk.length := by
  induction pieces generalizing reader with
  | nil =>
    have hd := Reader.empty_contents_disk B reader hr hc
    refine ⟨[], reader, rfl, rfl, rfl, ?_, hr, hc, ?_⟩
    · simp
    · simp [hd]
  | cons p rest ih =>
    obtain ⟨t, ht, hv, hs, hw, hn⟩ := copy_prefix B p rest.flatten
      ⟨reader, Writer.empty⟩ ⟨hr, Writer.empty_valid B hB⟩ hc
    have hw' : t.target.contents = p := by simpa [Writer.empty, Writer.contents] using hw
    obtain ⟨files, finalReader, hf, hcontents, hcounts, hvalid, hrv, hrem, hread⟩ :=
      ih t.source hv.1 hs
    refine ⟨t.target.finish :: files, finalReader, ?_, ?_, ?_, ?_, hrv, hrem, ?_⟩
    · simp only [List.map_cons, splitFiles, ht, hf]
    · simp only [List.map_cons, Writer.finish_contents, hw', hcontents]
    · simp only [List.map_cons, hcounts, Writer.finish_count B _ hv.2, hw', pack_count]
    · intro file hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact writer_finish_valid B hB _ hv.2
      · exact hvalid file hm
    · rw [hread]
      exact hn

/-- Join separately stored interval files using a single persistent output
writer. Each source file is read once; the output is packed across boundaries. -/
def joinFiles (B : ℕ) : List (List (List α)) → Writer α → Option (Writer α × ℕ)
  | [], writer => some (writer, 0)
  | file :: files, writer =>
      match run B file.flatten.length ⟨Reader.fromDisk file, writer⟩ with
      | none => none
      | some t =>
          match joinFiles B files t.target with
          | none => none
          | some (finalWriter, reads) => some (finalWriter, t.source.reads + reads)

theorem joinFiles_correct (B : ℕ) (files : List (List (List α)))
    (writer : Writer α) (hw : writer.Valid B)
    (hf : ∀ file ∈ files, (Reader.fromDisk file).Valid B) :
    ∃ finalWriter, joinFiles B files writer = some (finalWriter, (files.map List.length).sum) ∧
      finalWriter.Valid B ∧
      finalWriter.contents = writer.contents ++ (files.map List.flatten).flatten := by
  induction files generalizing writer with
  | nil => exact ⟨writer, rfl, hw, by simp⟩
  | cons file rest ih =>
    have hr := hf file (by simp)
    obtain ⟨t, ht, hv, hs, hc, hn⟩ := copy_prefix B file.flatten []
      ⟨Reader.fromDisk file, writer⟩ ⟨hr, hw⟩ (by simp [Reader.contents, Reader.fromDisk])
    have hd := Reader.empty_contents_disk B t.source hv.1 hs
    have hreads : t.source.reads = file.length := by simpa [hd, Reader.fromDisk] using hn
    obtain ⟨finalWriter, hjoin, hvalid, hcontents⟩ := ih t.target hv.2
      (fun file hm => hf file (by simp [hm]))
    refine ⟨finalWriter, ?_, hvalid, ?_⟩
    · simp only [joinFiles, ht, hjoin, hreads, List.map_cons, List.sum_cons]
    · rw [hcontents, hc]
      simp only [List.map_cons, List.flatten_cons, List.append_assoc]

theorem pack_nonempty (B : ℕ) (hB : 0 < B) (xs : List α) :
    ∀ block ∈ pack B hB xs, 0 < block.length := by
  induction xs using pack.induct B hB with
  | case1 => simp [pack]
  | case2 a rest ih =>
    intro block hb
    rw [pack] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only [List.length_take, List.length_cons]
      omega
    · exact ih block hb

theorem pack_reader_valid (B : ℕ) (hB : 0 < B) (xs : List α) :
    (Reader.fromDisk (pack B hB xs)).Valid B := by
  refine ⟨?_, hB⟩
  intro block hb
  exact ⟨pack_nonempty B hB xs block hb, block_size_bound B hB xs block hb⟩

end CSL.StreamCopy


