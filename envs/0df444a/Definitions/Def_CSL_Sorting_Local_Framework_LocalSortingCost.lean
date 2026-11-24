-- Prove2me | Definitions.Def_CSL_Sorting_Local_Framework_LocalSortingCost
-- name    : CSL_Sorting_Local_Framework_LocalSortingCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:56:24.072319+00:00
-- url     : https://prove2.me/theorems/267491b0-180c-4a7d-8a2d-7f6e872afea0
-- title:
--   Coded sorting library: Sorting / Local / Framework / LocalSortingCost
-- statement:
--   Module `CodedSorting.Sorting.Local.Framework.LocalSortingCost` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Shared-buffer in-memory sorting of consecutive short columns.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.Local.Framework.LocalSortingCost

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_StreamCopy
import Definitions.Def_CSL_Shared_Programs_LocalTrace

section BatchMemorySort
/-! Shared-buffer in-memory sorting of consecutive short columns. -/
namespace CSL.BatchMemorySort
open BucketMachine BucketReader StreamCopy
variable {α : Type*}

/-- Read a prescribed number of records into RAM, retaining the partially
consumed input block between columns. -/
def readRecords : ℕ → Reader α → Option (List α × Reader α)
  | 0, reader => some ([], reader)
  | n + 1, reader =>
      match reader.pop with
      | none => none
      | some (a, next) =>
          match readRecords n next with
          | none => none
          | some (tail, finalReader) => some (a :: tail, finalReader)

theorem readRecords_correct (B : ℕ) (front back : List α) (reader : Reader α)
    (hr : reader.Valid B) (hc : reader.contents = front ++ back) :
    ∃ finalReader, readRecords front.length reader = some (front, finalReader) ∧
      finalReader.Valid B ∧ finalReader.contents = back ∧
      finalReader.reads + finalReader.disk.length = reader.reads + reader.disk.length := by
  induction front generalizing reader with
  | nil => exact ⟨reader, rfl, hr, by simpa using hc, rfl⟩
  | cons a rest ih =>
    have hc' : reader.contents = a :: (rest ++ back) := by simpa using hc
    obtain ⟨next, hp⟩ := Reader.pop_exists B reader hr a _ hc'
    have hv := Reader.pop_valid B reader next a hr hp
    have hnext : next.contents = rest ++ back := by
      have h := Reader.pop_contents reader next a hp
      rw [hc'] at h
      exact (List.cons.inj h).2.symm
    obtain ⟨finalReader, he, hfinal, htail, hcount⟩ := ih next hv hnext
    refine ⟨finalReader, ?_, hfinal, htail, hcount.trans (Reader.pop_conservation _ _ _ hp)⟩
    simp only [List.length_cons, readRecords, hp, he]

def appendRecords (B : ℕ) (xs : List α) (writer : Writer α) : Writer α :=
  xs.foldl (fun s a => s.push B a) writer

theorem appendRecords_contents (B : ℕ) (xs : List α) (writer : Writer α) :
    (appendRecords B xs writer).contents = writer.contents ++ xs := by
  induction xs generalizing writer with
  | nil => simp [appendRecords]
  | cons a rest ih =>
    change (appendRecords B rest (writer.push B a)).contents = _
    rw [ih, Writer.push_contents]
    simp [List.append_assoc]

theorem appendRecords_valid (B : ℕ) (xs : List α) (writer : Writer α)
    (hw : writer.Valid B) : (appendRecords B xs writer).Valid B := by
  induction xs generalizing writer with
  | nil => exact hw
  | cons a rest ih => exact ih _ (Writer.push_valid B writer a hw)

/-- RAM sorting itself is an internal-memory operation. The input and
output stream buffers persist across all column boundaries. -/
def run (B : ℕ) (ramSort : List α → List α) :
    List ℕ → Reader α → Writer α → Option (Reader α × Writer α)
  | [], reader, writer => some (reader, writer)
  | n :: rest, reader, writer =>
      match readRecords n reader with
      | none => none
      | some (column, nextReader) =>
          run B ramSort rest nextReader (appendRecords B (ramSort column) writer)

/-- Exact sequential input and output of a whole leaf batch. -/
theorem run_correct (B : ℕ) (ramSort : List α → List α)
    (columns : List (List α)) (reader : Reader α) (writer : Writer α)
    (hr : reader.Valid B) (hw : writer.Valid B) (hc : reader.contents = columns.flatten) :
    ∃ finalReader finalWriter,
      run B ramSort (columns.map List.length) reader writer = some (finalReader, finalWriter) ∧
      finalReader.Valid B ∧ finalWriter.Valid B ∧ finalReader.contents = [] ∧
      finalReader.reads = reader.reads + reader.disk.length ∧
      finalWriter.contents = writer.contents ++ (columns.map ramSort).flatten := by
  induction columns generalizing reader writer with
  | nil =>
    have hd := Reader.empty_contents_disk B reader hr hc
    exact ⟨reader, writer, rfl, hr, hw, hc, by simp [hd], by simp⟩
  | cons column rest ih =>
    obtain ⟨nextReader, he, hv, hn, hreads⟩ := readRecords_correct B column rest.flatten reader hr hc
    have hwv := appendRecords_valid B (ramSort column) writer hw
    obtain ⟨finalReader, finalWriter, hrun, hrv, hwv, hrem, hcount, houtput⟩ :=
      ih nextReader (appendRecords B (ramSort column) writer) hv hwv hn
    refine ⟨finalReader, finalWriter, ?_, hrv, hwv, hrem, ?_, ?_⟩
    · simp only [List.map_cons, run, he, hrun]
    · exact hcount.trans hreads
    · rw [houtput, appendRecords_contents]
      simp only [List.map_cons, List.flatten_cons, List.append_assoc]

/-- The batch pays for a packed scan of all columns together, rather than
one startup block for each short column. -/
theorem packed_batch_transfers (B : ℕ) (hB : 0 < B) (ramSort : List α → List α)
    (hp : ∀ xs, (ramSort xs).Perm xs) (columns : List (List α)) :
    ∃ finalReader finalWriter,
      run B ramSort (columns.map List.length) (Reader.fromDisk (pack B hB columns.flatten))
        Writer.empty = some (finalReader, finalWriter) ∧
      finalWriter.finish.flatten = (columns.map ramSort).flatten ∧
      finalReader.reads + finalWriter.finish.length =
        2 * ((columns.flatten.length + B - 1) / B) := by
  obtain ⟨reader, writer, he, _, hw, _, hr, hc⟩ := run_correct B ramSort columns
    (Reader.fromDisk (pack B hB columns.flatten)) Writer.empty
    (pack_reader_valid B hB columns.flatten) (Writer.empty_valid B hB)
    (by simp [Reader.contents, Reader.fromDisk, flatten_pack])
  have hlen : (columns.map ramSort).flatten.length = columns.flatten.length := by
    simp only [List.length_flatten, List.map_map]
    congr 1
    apply List.map_congr_left
    intro column _
    exact (hp column).length_eq
  have hc' : writer.contents = (columns.map ramSort).flatten := by
    simpa [Writer.empty, Writer.contents] using hc
  refine ⟨reader, writer, he, ?_, ?_⟩
  · rw [Writer.finish_contents, hc']
  · rw [hr, Writer.finish_count B writer hw, hc', hlen]
    simp [Reader.fromDisk, pack_count, Nat.two_mul]

/-- A current column, its sorted image, and the two pending stream buffers
fit in 2r+2B units. This conservative bound permits a non-in-place RAM sorter
whose only live data are its input and output columns. -/
theorem column_workspace (B R : ℕ) (column output : List α)
    (reader : Reader α) (writer : Writer α)
    (hr : reader.Valid B) (hw : writer.Valid B) (hn : column.length ≤ R)
    (hp : output.Perm column) :
    column.length + output.length + reader.pending.length + writer.pending.length ≤ 2 * R + 2 * B := by
  have hl := hp.length_eq
  have hread := hr.2
  have hwrite := hw.2
  omega

end CSL.BatchMemorySort
end BatchMemorySort

section LocalSortingCost
/-! Costs are computed from the trace emitted by the recursive sorter itself.
Leaf batches share block buffers across all columns. -/
namespace CSL.LocalSortingCost
open RecursiveColumnsort LocalShape BucketMachine

abbrev InterchangeCost := ℕ → ℕ → ℕ

def blockCount (B n : ℕ) := (n + B - 1) / B

def leafScan (B n : ℕ) := 2 * blockCount B n

/-- Padding, half-column shift, unshift, and removal of this call's padding.
Each pass reads its source stream and writes its destination stream. -/
def scanTransfers (B n s : ℕ) :=
  2 * blockCount B n + 4 * blockCount B (s ^ 4) +
    2 * blockCount B (s ^ 4 + s ^ 3)

def CallTree.inputSize : CallTree → ℕ
  | .leaf n => n
  | .node n _ _ _ _ _ => n

def CallTree.isLeaf : CallTree → Bool
  | .leaf _ => true
  | .node _ _ _ _ _ _ => false

structure BatchSummary where
  allLeaves : Bool
  volume : ℕ
  individualCost : ℕ

def batchCharge (B : ℕ) (summary : BatchSummary) :=
  if summary.allLeaves then leafScan B summary.volume else summary.individualCost

mutual
  def traceCost (B : ℕ) (exchangeCost : InterchangeCost) : CallTree → ℕ
    | .leaf n => leafScan B n
    | .node n s first second third fourth =>
        6 * exchangeCost (sizeExponent n) (s ^ 4) + scanTransfers B n s +
          batchCharge B (summarize B exchangeCost first) +
          batchCharge B (summarize B exchangeCost second) +
          batchCharge B (summarize B exchangeCost third) +
          batchCharge B (summarize B exchangeCost fourth)
  def summarize (B : ℕ) (exchangeCost : InterchangeCost) : List CallTree → BatchSummary
    | [] => ⟨true, 0, 0⟩
    | head :: tail =>
        let rest := summarize B exchangeCost tail
        ⟨CallTree.isLeaf head && rest.allLeaves, CallTree.inputSize head + rest.volume,
          traceCost B exchangeCost head + rest.individualCost⟩
end

theorem summarize_spec (B : ℕ) (exchangeCost : InterchangeCost) (trees : List CallTree) :
    summarize B exchangeCost trees =
      ⟨trees.all CallTree.isLeaf, (trees.map CallTree.inputSize).sum,
        (trees.map (traceCost B exchangeCost)).sum⟩ := by
  induction trees with
  | nil => rfl
  | cons head tail ih => simp [summarize, ih]

theorem blockCount_capacity (B : ℕ) (hB : 0 < B) (n : ℕ) :
    blockCount B n * B ≤ n + B := by
  have h := Nat.le_of_lt (pack_capacity B hB (List.replicate n ())).2
  simpa [pack_count, blockCount] using h

theorem leafScan_bound (B : ℕ) (hB : 0 < B) (n : ℕ) :
    leafScan B n * B ≤ 2 * (n + B) := by
  have h := blockCount_capacity B hB n
  unfold leafScan
  nlinarith

/-- Genuine leaf-batch scan costs agree with the charge used by the trace. -/
theorem leaf_batch_machine (B : ℕ) (hB : 0 < B) (ramSort : List ℕ → List ℕ)
    (hp : ∀ xs, (ramSort xs).Perm xs) (columns : List (List ℕ)) :
    ∃ reader writer,
      BatchMemorySort.run B ramSort (columns.map List.length)
        (BucketReader.Reader.fromDisk (pack B hB columns.flatten)) Writer.empty =
        some (reader, writer) ∧
      writer.finish.flatten = (columns.map ramSort).flatten ∧
      reader.reads + writer.finish.length = leafScan B columns.flatten.length := by
  exact BatchMemorySort.packed_batch_transfers B hB ramSort hp columns

theorem fits_inputSize {H fuel n : ℕ} {tree : CallTree}
    (h : LocalTrace.Fits H fuel n tree) : CallTree.inputSize tree = n := by
  cases h <;> rfl

private theorem sum_bound (trees : List CallTree) (f : CallTree → ℕ) (B A : ℕ)
    (h : ∀ tree ∈ trees, f tree * B ≤ A) : (trees.map f).sum * B ≤ trees.length * A := by
  induction trees with
  | nil => simp
  | cons tree rest ih =>
    have ht := h tree (by simp)
    have hr := ih (fun tree ht => h tree (by simp [ht]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- A short-column batch uses the shared-buffer machine. A recursive batch
may pay per child because each such child is at least one block long. -/
theorem batch_bound (B H fuel r D : ℕ) (hB : 0 < B) (hBH : B ≤ H) (hD : 1 ≤ D)
    (exchangeCost : InterchangeCost) (trees : List CallTree)
    (hf : ∀ tree ∈ trees, LocalTrace.Fits H fuel r tree)
    (hc : ∀ tree ∈ trees, traceCost B exchangeCost tree * B ≤ D * (r + B)) :
    batchCharge B (summarize B exchangeCost trees) * B ≤ 2 * D * trees.length * r + 2 * B := by
  have hv : (trees.map CallTree.inputSize).sum = trees.length * r := by
    have he : trees.map CallTree.inputSize = trees.map (fun _ => r) := by
      apply List.map_congr_left
      intro tree ht
      exact fits_inputSize (hf tree ht)
    rw [he]
    simp
  rw [summarize_spec]
  unfold batchCharge
  try dsimp only
  split
  · have hs := leafScan_bound B hB (trees.length * r)
    rw [hv]
    have hmul := Nat.mul_le_mul_right (trees.length * r) hD
    nlinarith
  · rename_i hnot
    have hr : B ≤ r := by
      by_contra h
      have hsmall : r ≤ 512 * H := by omega
      have hall : trees.all CallTree.isLeaf = true := by
        apply List.all_eq_true.mpr
        intro tree ht
        rw [(hf tree ht).leaf_of_small hsmall]
        rfl
      exact hnot hall
    have hsum := sum_bound trees (traceCost B exchangeCost) B (D * (r + B)) hc
    have hm := Nat.mul_le_mul_left (trees.length * D) hr
    nlinarith

theorem scan_bound (B : ℕ) (hB : 0 < B) (n : ℕ) (hn : 1 < n) (hBn : B ≤ n) :
    scanTransfers B n (sizeChoice n) * B ≤ 138 * n := by
  have hnB := blockCount_capacity B hB n
  have hpB := blockCount_capacity B hB (sizeChoice n ^ 4)
  have heB := blockCount_capacity B hB (sizeChoice n ^ 4 + sizeChoice n ^ 3)
  have hp := padding_lt n hn
  have hs : 1 ≤ sizeChoice n := Nat.one_le_pow _ _ (by norm_num)
  have hr : sizeChoice n ^ 3 ≤ sizeChoice n ^ 4 := by
    calc
      sizeChoice n ^ 3 ≤ sizeChoice n * sizeChoice n ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
      _ = sizeChoice n ^ 4 := by ring
  unfold scanTransfers
  nlinarith

/-- Exact finite-depth cost theorem over the actual execution trace.
The only algorithmic cost premise is a bound for the address-exchange
primitive at each nonterminal call. Four leaf batches share stream buffers. -/
theorem trace_cost_bound (B H C : ℕ) (hB : 0 < B) (hH : 0 < H) (hBH : B ≤ H)
    (exchangeCost : InterchangeCost)
    (hx : ∀ n, 512 * H < n → n ≤ H ^ 2 →
      exchangeCost (sizeExponent n) (sizeChoice n ^ 4) * B ≤ C * (sizeChoice n ^ 4 + B))
    (fuel n : ℕ) (tree : CallTree) (hn : n ≤ H ^ 2) (hf : LocalTrace.Fits H fuel n tree) :
    traceCost B exchangeCost tree * B ≤ 300 ^ fuel * (C + 2) * (n + B) := by
  induction fuel generalizing n tree with
  | zero =>
    rw [hf.leaf_of_zero]
    have hs := leafScan_bound B hB n
    simp only [traceCost, pow_zero, Nat.one_mul]
    nlinarith
  | succ fuel ih =>
    cases hf with
    | leaf _ _ hleaf =>
      have hs := leafScan_bound B hB n
      have hpow : 1 ≤ 300 ^ (fuel + 1) := Nat.one_le_pow _ _ (by omega)
      have hmul := Nat.mul_le_mul_right ((C + 2) * (n + B)) hpow
      simp only [traceCost]
      nlinarith
    | node hlarge hfirst hsecond hthird hfourth hf1 hf2 hf3 hf4 =>
      have h512 : 512 < n := by nlinarith
      have hrn := column_lt n h512
      have hrH : columnLength n ≤ H ^ 2 := by omega
      let D := 300 ^ fuel * (C + 2)
      have hpow : 1 ≤ 300 ^ fuel := Nat.one_le_pow _ _ (by omega)
      have hCD : C + 2 ≤ D := Nat.le_mul_of_pos_left _ (by omega)
      have hD : 1 ≤ D := by omega
      have h1 := batch_bound B H fuel (columnLength n) D hB hBH hD exchangeCost _ hf1
        (fun child hc => ih _ _ hrH (hf1 child hc))
      have h2 := batch_bound B H fuel (columnLength n) D hB hBH hD exchangeCost _ hf2
        (fun child hc => ih _ _ hrH (hf2 child hc))
      have h3 := batch_bound B H fuel (columnLength n) D hB hBH hD exchangeCost _ hf3
        (fun child hc => ih _ _ hrH (hf3 child hc))
      have h4 := batch_bound B H fuel (columnLength n) D hB hBH hD exchangeCost _ hf4
        (fun child hc => ih _ _ hrH (hf4 child hc))
      rw [hfirst] at h1
      rw [hsecond] at h2
      rw [hthird] at h3
      rw [hfourth] at h4
      have hBn : B ≤ n := by nlinarith
      have hscan := scan_bound B hB n (by omega) hBn
      have hexchange := hx n hlarge hn
      have hpad := padding_lt n (by omega)
      have hvolume := child_volume n (by omega)
      have hxBound : 6 * exchangeCost (sizeExponent n) (sizeChoice n ^ 4) * B ≤ 102 * C * n := by
        have hm := Nat.mul_le_mul_left C (show sizeChoice n ^ 4 + B ≤ 17 * n by omega)
        nlinarith only [hexchange, hm]
      have hvolumeD := Nat.mul_le_mul_left (2 * D) (Nat.le_of_lt hvolume)
      have hCDn := Nat.mul_le_mul_right n hCD
      have hpower : 300 ^ (fuel + 1) * (C + 2) = 300 * D := by
        try dsimp [D]
        rw [pow_succ]
        ring
      simp only [traceCost]
      rw [hpower]
      nlinarith only [h1, h2, h3, h4, hscan, hxBound, hvolumeD, hCDn, hBn,
        Nat.zero_le (D * B)]

mutual
  /-- Purely structural memory obligation for every RAM-sort leaf. -/
  def leavesFit (H : ℕ) : CallTree → Prop
    | .leaf n => n ≤ 512 * H
    | .node _ _ first second third fourth =>
        batchLeavesFit H first ∧ batchLeavesFit H second ∧
          batchLeavesFit H third ∧ batchLeavesFit H fourth
  def batchLeavesFit (H : ℕ) : List CallTree → Prop
    | [] => True
    | tree :: rest => leavesFit H tree ∧ batchLeavesFit H rest
end

theorem batchLeavesFit_of_mem (H : ℕ) (trees : List CallTree)
    (h : ∀ tree ∈ trees, leavesFit H tree) : batchLeavesFit H trees := by
  induction trees with
  | nil => trivial
  | cons tree rest ih => exact ⟨h tree (by simp), ih (fun tree ht => h tree (by simp [ht]))⟩

def iterColumn : ℕ → ℕ → ℕ
  | 0, n => n
  | fuel + 1, n => iterColumn fuel (columnLength n)

/-- Every actual leaf is small, including the forced leaves at depth zero. -/
theorem leaves_fit_of_iter {H fuel n : ℕ} {tree : CallTree}
    (hf : LocalTrace.Fits H fuel n tree) (hn : iterColumn fuel n ≤ 512 * H) :
    leavesFit H tree := by
  induction fuel generalizing n tree with
  | zero => rw [hf.leaf_of_zero]; exact hn
  | succ fuel ih =>
    cases hf with
    | leaf _ _ hleaf =>
      rcases hleaf with hzero | hsmall
      · omega
      · exact hsmall
    | node _ _ _ _ _ h1 h2 h3 h4 =>
      exact ⟨batchLeavesFit_of_mem H _ (fun t ht => ih (h1 t ht) hn),
        batchLeavesFit_of_mem H _ (fun t ht => ih (h2 t ht) hn),
        batchLeavesFit_of_mem H _ (fun t ht => ih (h3 t ht) hn),
        batchLeavesFit_of_mem H _ (fun t ht => ih (h4 t ht) hn)⟩

theorem three_level_leaves_fit {H n : ℕ} {tree : CallTree}
    (hH : 0 < H) (hn : n ≤ H ^ 2) (hf : LocalTrace.Fits H 3 n tree) :
    leavesFit H tree := by
  apply leaves_fit_of_iter hf
  have h := LocalShape.three_levels_fit n H hH hn
  change columnLength (columnLength (columnLength n)) ≤ 512 * H
  omega

/-- Ready-to-compose local scan factor for a three-level execution trace.
It includes the startup term and proves every RAM leaf meets its cutoff. -/
theorem local_trace_bound (B H C : ℕ) (hB : 0 < B) (hH : 0 < H) (hBH : B ≤ H)
    (exchangeCost : InterchangeCost)
    (hx : ∀ n, 512 * H < n → n ≤ H ^ 2 →
      exchangeCost (sizeExponent n) (sizeChoice n ^ 4) * B ≤ C * (sizeChoice n ^ 4 + B))
    (n : ℕ) (tree : CallTree) (hn : n ≤ H ^ 2) (hf : LocalTrace.Fits H 3 n tree) :
    traceCost B exchangeCost tree * B ≤ 27000000 * (C + 2) * (n + B) ∧ leavesFit H tree := by
  constructor
  · simpa using trace_cost_bound B H C hB hH hBH exchangeCost hx 3 n tree hn hf
  · exact three_level_leaves_fit hH hn hf

end CSL.LocalSortingCost
end LocalSortingCost


