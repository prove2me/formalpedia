-- Prove2me | Definitions.Def_Submission_ThreeSum_LightModuloCounts
-- name    : Submission_ThreeSum_LightModuloCounts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:38:12.154607+00:00
-- url     : https://prove2.me/theorems/b36e3196-0aa2-4b1e-9f17-a192ab0c289a
-- title:
--   Light Modulo Counts
-- statement:
--   Definitions and structural lemmas for Light Modulo Counts, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightModuloCounts.lean

import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightCyclic
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_LightCyclic_program_procs
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs

set_option autoImplicit false
namespace ThreeSum.LightModuloCounts
open Light ThreeSum.LightResidues ThreeSum.LightResidueHistogram
open ThreeSum.KaratsubaInterface ThreeSum.CyclicFold
variable {lim : Limits} {P : Program} {d : ℕ}
def body (pCapacity pHist pCyclic pResidues pLookup : ℕ) : Stmt :=
  .call pCapacity [v 6] 9 ;;
  .set 10 (v 8 +' v 9) ;;
  .set 11 (v 8 +' k 2 *' v 9) ;;
  .set 12 (v 8 +' k 3 *' v 9) ;;
  .set 13 (v 8 +' k 5 *' v 9) ;;
  .set 14 (v 13 +' v 7) ;;
  .call pHist [v 1, v 11, v 4, v 6, v 9, v 13, v 14, k 0 -' k 1] 15 ;;
  .call pHist [v 2, v 10, v 5, v 6, v 9, v 13, v 14, k 1] 15 ;;
  .call pCyclic [v 9, v 10, v 11, v 12, v 8, v 14, v 6] 15 ;;
  .call pResidues [v 0, v 13, v 3, v 6, v 14, k 1] 15 ;;
  .call pLookup [v 13, v 8, v 3, v 6] 0
def time (p nA nB nC U : ℕ) : ℕ :=
  LightCapacity.time p + LightResidueHistogram.time nB (capacity p) U +
    LightResidueHistogram.time nC (capacity p) U +
    LightCyclic.combinedTime (Nat.clog 2 p) p +
    residuesTime nA U + LightLookupSum.time nA + 400
def space (free p N U : ℕ) : ℕ :=
  free + 13 * capacity p + N + Nat.log 2 (U+1) + 2
def word (p N U : ℕ) : ℕ :=
  LightKaratsuba.wordBound (capacity p) N + 4*U + 4*p + 16 + N^3
structure Procs (P : Program) (pMain : ℕ) where
  pCapacity : ℕ
  pHist : ℕ
  pCyclic : ℕ
  pResidues : ℕ
  pEmod : ℕ
  pHistogram : ℕ
  pMultiply : ℕ
  pHalf : ℕ
  pLinear : ℕ
  pFill : ℕ
  pLookup : ℕ
  main : P[pMain]? = some (body pCapacity pHist pCyclic pResidues pLookup)
  capacity : P[pCapacity]? = some LightCapacity.body
  hist : P[pHist]? = some (LightResidueHistogram.body pResidues pHistogram)
  residues : P[pResidues]? = some (residuesBody pEmod)
  emod : P[pEmod]? = some emodBody
  histogram : P[pHistogram]? = some (LightHistogram.histogramBody pFill)
  cyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear)
  multiply : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill
  lookup : P[pLookup]? = some LightLookupSum.body
def program : Program :=
  [body 1 2 6 3 11, LightCapacity.body, LightResidueHistogram.body 3 5,
    residuesBody 4, emodBody, LightHistogram.histogramBody 10, LightCyclic.body 7 9,
    LightKaratsuba.body 7 8 9 10, halfBody, LightArray.linearBody, fillBody,
    LightLookupSum.body]
def program_procs : Procs program 0 where
  pCapacity := 1
  pHist := 2
  pCyclic := 6
  pResidues := 3
  pEmod := 4
  pHistogram := 5
  pMultiply := 7
  pHalf := 8
  pLinear := 9
  pFill := 10
  pLookup := 11
  main := rfl
  capacity := rfl
  hist := rfl
  residues := rfl
  emod := rfl
  histogram := rfl
  cyclic := rfl
  multiply := ⟨rfl, rfl, rfl, rfl⟩
  lookup := rfl
end ThreeSum.LightModuloCounts


