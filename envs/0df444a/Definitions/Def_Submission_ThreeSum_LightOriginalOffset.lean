-- Prove2me | Definitions.Def_Submission_ThreeSum_LightOriginalOffset
-- name    : Submission_ThreeSum_LightOriginalOffset
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:41:17.136191+00:00
-- url     : https://prove2.me/theorems/c97caf32-2a56-45ab-87e5-2407cf19f7f5
-- title:
--   Light Original Offset
-- statement:
--   Definitions and structural lemmas for Light Original Offset, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalOffset.lean

import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightOriginalOffset
open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
def selected (p : ℕ) [NeZero p] (left right : ℕ → ℤ) (nLeft nRight : ℕ) : ℕ :=
  LightBalancedOffset.offset (signedHistogram p 1 right nRight)
    (signedHistogram p 1 left nLeft)
def body (pCapacity pHist pOffset : ℕ) : Stmt :=
  .call pCapacity [v 4] 7 ;;
  .set 8 (v 6 +' v 7) ;;
  .set 9 (v 6 +' k 2 *' v 7) ;;
  .set 10 (v 6 +' k 3 *' v 7) ;;
  .set 11 (v 6 +' k 5 *' v 7) ;;
  .set 12 (v 11 +' v 5) ;;
  .call pHist [v 0,v 9,v 2,v 4,v 7,v 11,v 12,k 0 -' k 1] 13 ;;
  .call pHist [v 1,v 8,v 3,v 4,v 7,v 11,v 12,k 1] 13 ;;
  .call pOffset [v 7,v 8,v 9,v 10,v 6,v 12,v 4] 0
def time (p nLeft nRight U : ℕ) : ℕ := LightCapacity.time p+
  LightResidueHistogram.time nLeft (capacity p) U+
  LightResidueHistogram.time nRight (capacity p) U+
  LightBalancedOffset.time (Nat.clog 2 p) p+300
def space (free p N U : ℕ) : ℕ := free+13*capacity p+N+Nat.log 2 (U+1)+2
def word (p N U : ℕ) : ℕ := LightKaratsuba.wordBound (capacity p) N+4*U+4*p+16
structure Procs (P : Program) (pMain : ℕ) where
  pCapacity : ℕ
  pHist : ℕ
  pResidues : ℕ
  pEmod : ℕ
  pHistogram : ℕ
  pFill : ℕ
  pOffset : ℕ
  pCyclic : ℕ
  pMultiply : ℕ
  pHalf : ℕ
  pLinear : ℕ
  pMinimum : ℕ
  capacityProc : P[pCapacity]? = some LightCapacity.body
  histogram : P[pHist]? = some (LightResidueHistogram.body pResidues pHistogram)
  residues : P[pResidues]? = some (residuesBody pEmod)
  emod : P[pEmod]? = some emodBody
  count : P[pHistogram]? = some (LightHistogram.histogramBody pFill)
  offset : P[pOffset]? = some (LightBalancedOffset.body pCyclic pMinimum)
  cyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear)
  karatsuba : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill
  minimum : P[pMinimum]? = some LightMinimum.body
  main : P[pMain]? = some (body pCapacity pHist pOffset)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 2 7,LightCapacity.body,LightResidueHistogram.body 3 5,residuesBody 4,
    emodBody,LightHistogram.histogramBody 6,fillBody,LightBalancedOffset.body 8 12,
    LightCyclic.body 9 11,LightKaratsuba.body 9 10 11 6,halfBody,
    LightArray.linearBody,LightMinimum.body]
def programProcs : Procs program 0 :=
  ⟨1,2,3,4,5,6,7,8,9,10,11,12,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩
end ThreeSum.LightOriginalOffset


