-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreCell
-- name    : Submission_ThreeSum_LightBandWeightedScoreCell
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:23:32.67702+00:00
-- url     : https://prove2.me/theorems/bdd4895f-38be-4cf7-ae1d-0c9acb711e33
-- title:
--   Light Band Weighted Score Cell
-- statement:
--   Definitions and structural lemmas for Light Band Weighted Score Cell, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandWeightedScoreCell.lean

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreSlice
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_ReportingHostRelocation_lookup

set_option autoImplicit false
namespace ThreeSum.LightBandWeightedScoreCell
open Light BandCandidateRows BandWeightedScore
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def body (pLength pScore : ℕ) : Stmt :=
  .set 12 (M (v 7)) ;;
  .ite (v 12 =' k 1)
    (.set 13 (M (v 7 +' k 1)) ;;
     .set 14 (M (v 7 +' k 2)) ;;
     .set 15 (M (v 7 +' k 3)) ;;
     .call pLength [v 3,v 6,v 13] 16 ;;
     .call pLength [v 4,v 6,v 14] 17 ;;
     .call pLength [v 5,v 6,v 15] 18 ;;
     .call pScore [v 0 +' v 13 *' v 6,v 1 +' v 14 *' v 6,v 2 +' v 15 *' v 6,
       v 16,v 17,v 18,v 8,v 6,v 9,v 10,v 11] 0)
    (.set 0 (k 0))
def time (maxMod g s U : ℕ) : ℕ :=
  3*LightBandWeightedScoreSlice.time+LightWeightedScore.runtimeTime maxMod g g g s U+250
def word (maxMod nA nB nC g s U : ℕ) : ℕ :=
  LightWeightedScore.word maxMod g s U+nA+nB+nC+g+8
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g rec q aux s free maxMod U : ℕ}
def program : Program := LightWeightedScore.program ++
  [LightBandWeightedScoreSlice.body,body 14 0]
def programProcs : LightWeightedScore.Procs program 0 where
  pCount := 2
  pJoint := 1
  count :=
    { pCapacity := 3, pHist := 4, pCyclic := 8, pResidues := 5, pEmod := 6,
      pHistogram := 7, pMultiply := 9, pHalf := 10, pLinear := 11, pFill := 12, pLookup := 13,
      main := rfl, capacity := rfl, hist := rfl, residues := rfl, emod := rfl,
      histogram := rfl, cyclic := rfl, multiply := ⟨rfl,rfl,rfl,rfl⟩, lookup := rfl }
  main := rfl
  joint := rfl
end ThreeSum.LightBandWeightedScoreCell


