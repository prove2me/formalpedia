-- Prove2me | Definitions.Def_CSL_Shared_Programs_LocalToMSD
-- name    : CSL_Shared_Programs_LocalToMSD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:16:13.289798+00:00
-- url     : https://prove2.me/theorems/30bcce78-245c-4349-9de2-66c1e2d72209
-- title:
--   Coded sorting library: Shared / Programs / LocalToMSD
-- statement:
--   Module `CodedSorting.Shared.Programs.LocalToMSD` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Concrete constant-buffer interval materialization and gathering for 7.1.
--   The input rows are disk streams produced by local sorting. Each interval is
--   written to an aligned scratch file, then the directory is traversed in
--   key/row order. This adds one sequential pass to the manuscript's direct
--   interval-reading description, without changing its asymptotic bound.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.LocalToMSD

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Memory_FileTranspose
import Definitions.Def_CSL_Shared_Records_KeyRecordWords
import Definitions.Def_CSL_Sorting_Local_Columnsort_GroupedRecursiveColumnsort

section IntervalMachine
/-! Concrete constant-buffer interval materialization and gathering for 7.1.
The input rows are disk streams produced by local sorting. Each interval is
written to an aligned scratch file, then the directory is traversed in
key/row order. This adds one sequential pass to the manuscript's direct
interval-reading description, without changing its asymptotic bound. -/
namespace CSL.IntervalMachine
open BucketMachine BucketReader StreamCopy ExternalMSD
variable {α : Type*} {K : ℕ}

abbrev Directory (α : Type*) := List (List (List (List α)))

/-- Read each sorted row sequentially and materialize its K digit intervals.
Completed files are disk objects; there is only one active reader and writer. -/
def materialize (key : α → Fin K) (B : ℕ) (hB : 0 < B) :
    List (List α) → Option (Directory α × ℕ)
  | [] => some ([], 0)
  | row :: rows =>
      match splitFiles B ((List.finRange K).map (fun k => (bucket key row k).length))
        (Reader.fromDisk (pack B hB row)) with
      | none => none
      | some (files, reader) =>
          match materialize key B hB rows with
          | none => none
          | some (directory, reads) => some (files :: directory, reader.reads + reads)

theorem materialize_correct (key : α → Fin K) (B : ℕ) (hB : 0 < B)
    (rows : List (List α))
    (hs : ∀ row ∈ rows, row.Pairwise (fun a b => key a ≤ key b)) :
    ∃ directory,
      materialize key B hB rows = some (directory, transferSum B hB rows) ∧
      directory.map (List.map List.flatten) = rows.map (fun row => (List.finRange K).map (bucket key row)) ∧
      directory.flatten.map List.length = (fragments key rows).map (fun p => (pack B hB p).length) ∧
      (∀ file ∈ directory.flatten, (Reader.fromDisk file).Valid B) := by
  induction rows with
  | nil => exact ⟨[], rfl, rfl, rfl, by simp⟩
  | cons row rows ih =>
    let pieces := (List.finRange K).map (bucket key row)
    have hpieces : pieces.flatten = row := collect_sorted key row (hs row (by simp))
    have hc : (Reader.fromDisk (pack B hB row)).contents = pieces.flatten := by
      simpa [Reader.contents, Reader.fromDisk, flatten_pack] using hpieces.symm
    obtain ⟨files, reader, hexec, hcontents, hcounts, hv, _, _, hreads⟩ :=
      splitFiles_correct B hB pieces (Reader.fromDisk (pack B hB row))
        (pack_reader_valid B hB row) hc
    obtain ⟨directory, htail, htailcontents, htailcounts, htailvalid⟩ :=
      ih (fun row hr => hs row (by simp [hr]))
    refine ⟨files :: directory, ?_, ?_, ?_, ?_⟩
    · have he : pieces.map List.length =
          (List.finRange K).map (fun k => (bucket key row k).length) := by
        simp [pieces, List.map_map, Function.comp_def]
      rw [he] at hexec
      rw [materialize, hexec, htail]
      simp only [hreads, Reader.fromDisk, transferSum, List.map_cons, List.sum_cons, Nat.zero_add]
    · simp only [List.map_cons, hcontents, htailcontents]
      rfl
    · simp only [List.flatten_cons, List.map_append, hcounts, htailcounts,
        fragments, List.flatMap_cons, List.map_append]
      rfl
    · intro file hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hv file hf
      · exact htailvalid file hf

theorem directory_shape (key : α → Fin K) (rows : List (List α)) (directory : Directory α)
    (hc : directory.map (List.map List.flatten) =
      rows.map (fun row => (List.finRange K).map (bucket key row))) :
    ∀ files ∈ directory, files.length = K := by
  intro files hf
  have hm : files.map List.flatten ∈ directory.map (List.map List.flatten) :=
    List.mem_map.mpr ⟨files, hf, rfl⟩
  rw [hc] at hm
  obtain ⟨row, _, he⟩ := List.mem_map.mp hm
  have hl := congrArg List.length he
  simpa using hl.symm

/-- Reordering the directory changes no file and no block-transfer count. -/
theorem selected_files_perm (key : α → Fin K) (rows : List (List α)) (directory : Directory α)
    (hc : directory.map (List.map List.flatten) =
      rows.map (fun row => (List.finRange K).map (bucket key row))) :
    (FileTranspose.select K [] directory).Perm directory.flatten :=
  FileTranspose.select_perm K [] directory (directory_shape key rows directory hc)

theorem selected_contents (key : α → Fin K) (rows : List (List α)) (directory : Directory α)
    (hc : directory.map (List.map List.flatten) =
      rows.map (fun row => (List.finRange K).map (bucket key row))) :
    ((FileTranspose.select K [] directory).map List.flatten).flatten = gather key rows := by
  rw [FileTranspose.map_select, hc]
  simp only [FileTranspose.select, List.flatMap_map, List.map_map, Function.comp_def]
  have hget (k : Fin K) (row : List α) :
      ((List.finRange K).map (bucket key row))[k.val]?.getD [] = bucket key row k := by
    simp [List.getElem?_map, List.getElem?_eq_getElem]
  simp only [List.flatten_nil]
  simp_rw [hget]
  rw [List.flatten_eq_flatMap, List.flatMap_assoc]
  simp [List.flatMap_map, gather]

/-- Physical block output and the charged transfer count. Descriptor visits
are charged one write and one read per row/key entry, independently of data. -/
def partition (key : α → Fin K) (B : ℕ) (hB : 0 < B) (rows : List (List α)) :
    Option (List (List α) × ℕ) :=
  match materialize key B hB rows with
  | none => none
  | some (directory, reads) =>
      match joinFiles B (FileTranspose.select K [] directory) Writer.empty with
      | none => none
      | some (writer, joiningReads) =>
          some (writer.finish, reads + (directory.flatten.map List.length).sum +
            joiningReads + writer.finish.length + 2 * rows.length * K)

/-- Concrete execution has exactly the block count used in the mathematical
MSD recurrence. The data output is byte-for-byte the specified gather order. -/
theorem partition_correct (key : α → Fin K) (B : ℕ) (hB : 0 < B)
    (rows : List (List α))
    (hs : ∀ row ∈ rows, row.Pairwise (fun a b => key a ≤ key b)) :
    ∃ blocks, partition key B hB rows = some (blocks, gatheringTransfers key B hB rows) ∧
      blocks.flatten = gather key rows ∧
      (Reader.fromDisk blocks).Valid B := by
  obtain ⟨directory, hmaterialize, hcontents, hcounts, hvalid⟩ := materialize_correct key B hB rows hs
  have hp := selected_files_perm key rows directory hcontents
  have hselected : ∀ file ∈ FileTranspose.select K [] directory, (Reader.fromDisk file).Valid B := by
    intro file hf
    exact hvalid file (hp.mem_iff.mp hf)
  obtain ⟨writer, hjoin, hw, houtput⟩ :=
    joinFiles_correct B (FileTranspose.select K [] directory) Writer.empty (Writer.empty_valid B hB) hselected
  have ho : writer.contents = gather key rows := by
    rw [selected_contents key rows directory hcontents] at houtput
    simpa [Writer.empty, Writer.contents] using houtput
  have hreads : ((FileTranspose.select K [] directory).map List.length).sum =
      transferSum B hB (fragments key rows) := by
    rw [(hp.map List.length).sum_eq, hcounts]
    rfl
  have hwrite : writer.finish.length = (pack B hB (gather key rows)).length := by
    rw [Writer.finish_count B writer hw, ho, pack_count]
  refine ⟨writer.finish, ?_, ?_, writer_finish_valid B hB writer hw⟩
  · simp only [partition, hmaterialize, hjoin, hcounts, hreads, hwrite]
    unfold gatheringTransfers transferSum
    congr 2
    omega
  · rw [Writer.finish_contents, ho]

/-- Instantiation on the locally sorted H² chunks. Local sorting remains
an explicit interface; the subsequent physical partition is implemented. -/
theorem local_partition_correct (base : ℕ) (hb : 0 < base) (B : ℕ) (hB : 0 < B)
    (H : ℕ) (hH : 0 < H) (hBH : B ≤ H) (hbase : base ≤ H)
    (localSort : MSD.LocalSorter) (hc : MSD.LocalCorrect localSort)
    (fuel : ℕ) (xs : List ℕ) (hn : H ^ 2 ≤ xs.length) :
    ∃ blocks transfers,
      partition (MSD.digit base hb fuel) B hB (prepare base hb H hH localSort fuel xs) =
        some (blocks, transfers) ∧
      blocks.flatten = gather (MSD.digit base hb fuel) (prepare base hb H hH localSort fuel xs) ∧
      blocks.flatten.Perm xs ∧ transfers ≤ 14 * xs.length / B + 1 := by
  have hsorted : ∀ row ∈ prepare base hb H hH localSort fuel xs,
      row.Pairwise (fun a b => MSD.digit base hb fuel a ≤ MSD.digit base hb fuel b) := by
    intro row hr
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp hr
    exact (hc _ source).2
  obtain ⟨blocks, hexec, hcontents, _⟩ := partition_correct (MSD.digit base hb fuel) B hB
    (prepare base hb H hH localSort fuel xs) hsorted
  refine ⟨blocks, _, hexec, hcontents, ?_, ?_⟩
  · rw [hcontents]
    exact (gather_perm _ _).trans (prepare_perm base hb H hH localSort hc fuel xs)
  · exact gathering_scan_count _ B H hB hH hBH hbase hb _ (fun row => (hc _ row).1) xs hn

end CSL.IntervalMachine
end IntervalMachine

section LocalToMSD
/-! Connect the actual recursive Columnsort execution to the high-digit
external sort. Only the address-interchange implementation/cost interface
remains external to this composition; no local-sort oracle is assumed. -/
namespace CSL.LocalToMSD
open RecursiveColumnsort LocalShape LocalSortingCost KeyRecords

def localSorter (H : ℕ) (hH : 0 < H) : MSD.LocalSorter :=
  adapt (localRun H hH 3)

def localCost (B H : ℕ) (hH : 0 < H) (exchangeCost : InterchangeCost) : MSD.LocalCost :=
  adaptCost B exchangeCost (localRun H hH 3)

theorem localSorter_correct (H : ℕ) (hH : 0 < H) : MSD.LocalCorrect (localSorter H hH) :=
  adapt_correct (localRun H hH 3) (localRun_correct H hH 3)

/-- This cost belongs to the same execution which produced the sorted list. -/
theorem localCost_bound (B H C : ℕ) (hB : 0 < B) (hH : 0 < H) (hBH : B ≤ H)
    (exchangeCost : InterchangeCost)
    (hx : ∀ n, 512 * H < n → n ≤ H ^ 2 →
      exchangeCost (sizeExponent n) (sizeChoice n ^ 4) * B ≤ C * (sizeChoice n ^ 4 + B))
    (key : ℕ → ℕ) (xs : List ℕ) (hn : xs.length ≤ H ^ 2) :
    localCost B H hH exchangeCost key xs * B ≤ 27000000 * (C + 2) * (xs.length + B) := by
  exact (local_trace_bound B H C hB hH hBH exchangeCost hx xs.length
    (localRun H hH 3 xs.length (input key xs)).trace hn
    (localRun_trace_fits H hH 3 xs.length (input key xs))).1

theorem local_memory_cutoff (H : ℕ) (hH : 0 < H) (key : ℕ → ℕ) (xs : List ℕ)
    (hn : xs.length ≤ H ^ 2) :
    leavesFit H (localRun H hH 3 xs.length (input key xs)).trace :=
  three_level_leaves_fit hH hn (localRun_trace_fits H hH 3 xs.length (input key xs))

/-- The global sorter uses the proved recursive Columnsort implementation for local sorting. 
-/
def sort (base : ℕ) (hb : 0 < base) (H : ℕ) (hH : 0 < H) : ℕ → List ℕ → List ℕ :=
  ExternalMSD.sort base hb H hH (localSorter H hH)

def cost (base : ℕ) (hb : 0 < base) (B : ℕ) (hB : 0 < B)
    (H : ℕ) (hH : 0 < H) (exchangeCost : InterchangeCost) : ℕ → List ℕ → ℕ :=
  ExternalMSD.cost base hb B hB H hH (localSorter H hH) (localCost B H hH exchangeCost)

theorem sort_correct (base : ℕ) (hb : 0 < base) (H : ℕ) (hH : 0 < H)
    (fuel : ℕ) (xs : List ℕ) (hbound : ∀ x ∈ xs, x < base ^ fuel) :
    (sort base hb H hH fuel xs).Perm xs ∧
      (sort base hb H hH fuel xs).Pairwise (· ≤ ·) :=
  ExternalMSD.sort_correct base hb H hH (localSorter H hH)
    (localSorter_correct H hH) fuel xs hbound

/-- Closed finite-depth bound after instantiating the local cost contract
with its proved call-tree bound. The address-interchange primitive is the
single remaining algorithmic cost hypothesis. -/
theorem cost_bound (base : ℕ) (hb : 0 < base) (B : ℕ) (hB : 0 < B)
    (H C : ℕ) (hH : 0 < H) (hBH : B ≤ H) (hbase : base ≤ H)
    (exchangeCost : InterchangeCost)
    (hx : ∀ n, 512 * H < n → n ≤ H ^ 2 →
      exchangeCost (sizeExponent n) (sizeChoice n ^ 4) * B ≤ C * (sizeChoice n ^ 4 + B))
    (fuel : ℕ) (xs : List ℕ) :
    cost base hb B hB H hH exchangeCost fuel xs * B ≤
      ((4 * (27000000 * (C + 2)) + 15) * fuel + 27000000 * (C + 2)) * xs.length +
        27000000 * (C + 2) * B := by
  exact ExternalMSD.cost_depth_bound base hb B hB H hH hBH hbase (localSorter H hH)
    (localSorter_correct H hH) (localCost B H hH exchangeCost) (27000000 * (C + 2))
    (localCost_bound B H C hB hH hBH exchangeCost hx) fuel xs

/-- One actual global partition, using the newly verified local sorter and
the sequential physical interval machine from Section 7.1. -/
theorem digit_partition (base : ℕ) (hb : 0 < base) (B : ℕ) (hB : 0 < B)
    (H : ℕ) (hH : 0 < H) (hBH : B ≤ H) (hbase : base ≤ H)
    (fuel : ℕ) (xs : List ℕ) (hn : H ^ 2 ≤ xs.length) :
    ∃ blocks transfers,
      IntervalMachine.partition (MSD.digit base hb fuel) B hB
        (ExternalMSD.prepare base hb H hH (localSorter H hH) fuel xs) = some (blocks, transfers) ∧
      blocks.flatten = ExternalMSD.gather (MSD.digit base hb fuel)
        (ExternalMSD.prepare base hb H hH (localSorter H hH) fuel xs) ∧
      blocks.flatten.Perm xs ∧ transfers ≤ 14 * xs.length / B + 1 :=
  IntervalMachine.local_partition_correct base hb B hB H hH hBH hbase (localSorter H hH)
    (localSorter_correct H hH) fuel xs hn

end CSL.LocalToMSD
end LocalToMSD


