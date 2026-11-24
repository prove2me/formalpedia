-- Prove2me | Definitions.Def_CSL_Shared_Words_RecordWidthTraceCost
-- name    : CSL_Shared_Words_RecordWidthTraceCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:31:42.839655+00:00
-- url     : https://prove2.me/theorems/b68d8bfb-1b6b-4624-acb1-4224611440be
-- title:
--   Coded sorting library: Shared / Words / RecordWidthTraceCost
-- statement:
--   Module `CodedSorting.Shared.Words.RecordWidthTraceCost` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Explicit scan charges for records occupying r physical words.
--   The exchange charge already covers every bit of a complete record. All
--   other scans and terminal batches below transfer r words per record. This
--   is a cost-annotation comparison on the actual Columnsort trace, not a claim
--   that a complete bounded-RAM implementation has already been constructed.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Words.RecordWidthTraceCost

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Programs_LocalToMSD
import Definitions.Def_CSL_Shared_Words_WordConvention

/-! Explicit scan charges for records occupying r physical words.
The exchange charge already covers every bit of a complete record. All
other scans and terminal batches below transfer r words per record. This
is a cost-annotation comparison on the actual Columnsort trace, not a claim
that a complete bounded-RAM implementation has already been constructed. -/
set_option autoImplicit false
namespace CSL.RecordWidthTraceCost
open RecursiveColumnsort LocalSortingCost

def leafCharge (B r n : ℕ) : ℕ := leafScan B (r*n)

def scanCharge (B r n s : ℕ) : ℕ :=
  2*blockCount B (r*n)+4*blockCount B (r*s^4)+
    2*blockCount B (r*(s^4+s^3))

def batchCharge (B r : ℕ) (summary : BatchSummary) : ℕ :=
  if summary.allLeaves then leafCharge B r summary.volume else summary.individualCost

mutual
  def traceCost (B r : ℕ) (exchangeCost : InterchangeCost) : CallTree → ℕ
    | .leaf n => leafCharge B r n
    | .node n s first second third fourth =>
      6*exchangeCost (LocalShape.sizeExponent n) (s^4)+scanCharge B r n s+
      batchCharge B r (summarize B r exchangeCost first)+
      batchCharge B r (summarize B r exchangeCost second)+
      batchCharge B r (summarize B r exchangeCost third)+
      batchCharge B r (summarize B r exchangeCost fourth)
  def summarize (B r : ℕ) (exchangeCost : InterchangeCost) : List CallTree → BatchSummary
    | [] => ⟨true,0,0⟩
    | head::tail =>
      let rest := summarize B r exchangeCost tail
      ⟨CallTree.isLeaf head && rest.allLeaves,CallTree.inputSize head+rest.volume,
        traceCost B r exchangeCost head+rest.individualCost⟩
end

theorem blockCount_scaled (B r n : ℕ) (hB : 0<B) :
    blockCount B (r*n) ≤ r*blockCount B n := by
  have hn : n≤blockCount B n*B := WordControl.frame_fits n B hB
  have hm := Nat.mul_le_mul_left r hn
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hB).2
  have hpos : 1≤r*n+B := by omega
  have hsub : r*n+B-1+1=r*n+B := Nat.sub_add_cancel hpos
  simp only [Nat.succ_mul]
  nlinarith only [hm,hsub]

theorem leafCharge_bound (B r n : ℕ) (hB : 0<B) :
    leafCharge B r n ≤ r*leafScan B n := by
  have h := blockCount_scaled B r n hB
  unfold leafCharge leafScan
  nlinarith only [h]

theorem scanCharge_bound (B r n s : ℕ) (hB : 0<B) :
    scanCharge B r n s ≤ r*scanTransfers B n s := by
  have h1 := blockCount_scaled B r n hB
  have h2 := blockCount_scaled B r (s^4) hB
  have h3 := blockCount_scaled B r (s^4+s^3) hB
  unfold scanCharge scanTransfers
  nlinarith only [h1,h2,h3]

theorem summarize_spec (B r : ℕ) (exchangeCost : InterchangeCost) (trees : List CallTree) :
    summarize B r exchangeCost trees =
      ⟨trees.all CallTree.isLeaf,(trees.map CallTree.inputSize).sum,
        (trees.map (traceCost B r exchangeCost)).sum⟩ := by
  induction trees with
  | nil => rfl
  | cons head tail ih => simp [summarize,ih]

private theorem sum_bound (r : ℕ) (f g : CallTree→ℕ) (trees : List CallTree)
    (h : ∀ t∈trees,f t≤r*g t) : (trees.map f).sum≤r*(trees.map g).sum := by
  induction trees with
  | nil => simp
  | cons t ts ih =>
    have hh := h t (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.map_cons,List.sum_cons]
    nlinarith only [hh,ht]

theorem batchCharge_bound (B r : ℕ) (hB : 0<B) (exchangeCost : InterchangeCost)
    (trees : List CallTree)
    (h : ∀ t∈trees,traceCost B r exchangeCost t≤r*LocalSortingCost.traceCost B exchangeCost t) :
    batchCharge B r (summarize B r exchangeCost trees) ≤
      r*LocalSortingCost.batchCharge B (LocalSortingCost.summarize B exchangeCost trees) := by
  rw [summarize_spec,LocalSortingCost.summarize_spec]
  unfold batchCharge LocalSortingCost.batchCharge
  try dsimp only
  split_ifs
  · exact leafCharge_bound B r _ hB
  · exact sum_bound r _ _ trees h

/-- This applies to every actual trace emitted by localRun. The factor r
also safely covers exchange calls, whose complete-record charge is kept
unchanged on the left side. -/
theorem traceCost_bound (B r H fuel n : ℕ) (hB : 0<B) (hr : 0<r)
    (exchangeCost : InterchangeCost) (tree : CallTree) (hf : LocalTrace.Fits H fuel n tree) :
    traceCost B r exchangeCost tree≤r*LocalSortingCost.traceCost B exchangeCost tree := by
  induction fuel generalizing n tree with
  | zero =>
    rw [hf.leaf_of_zero]
    exact leafCharge_bound B r n hB
  | succ fuel ih =>
    cases hf with
    | leaf => exact leafCharge_bound B r n hB
    | node hlarge hfirst hsecond hthird hfourth hf hs ht hu =>
      have h1 := batchCharge_bound B r hB exchangeCost _ (fun t hmem => ih _ t (hf t hmem))
      have h2 := batchCharge_bound B r hB exchangeCost _ (fun t hmem => ih _ t (hs t hmem))
      have h3 := batchCharge_bound B r hB exchangeCost _ (fun t hmem => ih _ t (ht t hmem))
      have h4 := batchCharge_bound B r hB exchangeCost _ (fun t hmem => ih _ t (hu t hmem))
      have hscan := scanCharge_bound B r n (LocalShape.sizeChoice n) hB
      have hex := Nat.le_mul_of_pos_left
        (6*exchangeCost (LocalShape.sizeExponent n) (LocalShape.sizeChoice n^4)) hr
      simp only [traceCost,LocalSortingCost.traceCost]
      nlinarith only [h1,h2,h3,h4,hscan,hex]

theorem localCost_bound (B r H : ℕ) (hB : 0<B) (hr : 0<r) (hH : 0<H)
    (exchangeCost : InterchangeCost) (key : ℕ→ℕ) (xs : List ℕ) :
    traceCost B r exchangeCost (localRun H hH 3 xs.length (KeyRecords.input key xs)).trace ≤
      r*LocalToMSD.localCost B H hH exchangeCost key xs :=
  traceCost_bound B r H 3 xs.length hB hr exchangeCost _
    (localRun_trace_fits H hH 3 xs.length (KeyRecords.input key xs))

end CSL.RecordWidthTraceCost


