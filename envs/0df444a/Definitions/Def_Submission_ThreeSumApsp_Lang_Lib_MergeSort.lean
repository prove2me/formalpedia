-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
-- name    : Submission_ThreeSumApsp_Lang_Lib_MergeSort
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:17:36.708603+00:00
-- url     : https://prove2.me/theorems/883a0854-936e-46da-8069-f9c5aaecec8d
-- title:
--   Merge Sort
-- statement:
--   Definitions and structural lemmas for Merge Sort, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
section
namespace Light
variable {lim : Limits} {P : Program}
namespace MergeSort
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Start : ℕ := 1
@[inherit_doc Len] abbrev Free : ℕ := 2
@[inherit_doc Len] abbrev Half : ℕ := 3
@[inherit_doc Len] abbrev Unused : ℕ := 4
end MergeSort
open MergeSort in
/-- The two sorted halves are merged into the cells from fr and copied back. -/
def sortJoin (pMerge pCopy : ℕ) : Stmt :=
  .call pMerge [v Start, v Half, v Start +' v Half, v Len -' v Half, v Free] Unused ;;
  .call pCopy [v Free, v Start, v Len] Unused
open MergeSort in
/-- sort(n, a, fr).  The parameters are the procedure numbers of sort itself, half, merge and
copy. -/
def sortBody (pSort pHalf pMerge pCopy : ℕ) : Stmt :=
  .ite (k 1 <' v Len) (
    .call pHalf [v Len] Half ;;
    .call pSort [v Half, v Start, v Free] Unused ;;
    .call pSort [v Len -' v Half, v Start +' v Half, v Free] Unused ;;
    sortJoin pMerge pCopy) .skip
def sortTime (n : ℕ) : ℕ := 61 * (n * Nat.clog 2 n) + 74 * (n - 1) + 4
namespace MergeSort
structure Procs (P : Program) (pSort pHalf pMerge pCopy : ℕ) : Prop where
  sort : P[pSort]? = some (sortBody pSort pHalf pMerge pCopy)
  half : P[pHalf]? = some halfBody
  merge : P[pMerge]? = some mergeBody
  copy : P[pCopy]? = some copyBody
def Sorted (μ : ℕ → ℤ) (a fr : ℕ) (L : List ℤ) (μ' : ℕ → ℤ) : Prop :=
  (∃ L' : List ℤ, Seg μ' a L' ∧ L'.Perm L ∧ L'.Pairwise (· ≤ ·)) ∧
    KeptBut μ μ' fr a L.length
variable {pSort pHalf pMerge pCopy : ℕ}
end MergeSort
end Light


