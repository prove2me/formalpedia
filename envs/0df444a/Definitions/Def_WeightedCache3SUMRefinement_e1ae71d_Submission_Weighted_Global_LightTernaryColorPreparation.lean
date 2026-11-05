-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparation
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:35:26.681192+00:00
-- url     : https://prove2.me/theorems/cce198a6-60fc-4897-817b-7c437044c3b1
-- title:
--   LightTernaryColorPreparation
-- statement:
--   Definitions and structural lemmas for LightTernaryColorPreparation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryColorPreparation.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPrelude
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedGlobalColorPreparation
open Light
set_option maxRecDepth 20000
def leftLibrary : Program := ReportingHostRelocation.program
  LightTernaryColorPrelude.program (LightTernarySignedMatrix.program false)
def rightLibrary : Program := ReportingHostRelocation.program leftLibrary
  (LightTernarySignedMatrix.program true)
def carryLibrary : Program := ReportingHostRelocation.program rightLibrary LightTernaryCarryCodes.program
def libraries : Program := ReportingHostRelocation.program carryLibrary LightTernaryRequesterMatrix.program
def fields : List ℕ := [6,7,8,9,10,11,19,20,21,23,24,25,26,27,12,13,14,15,16]
def stores : ℕ→List ℕ→Stmt
  | _,[]=>.skip
  | offset,reg::rest=>.store (v 18 +' k offset) (v reg) ;; stores (offset+1) rest
def buildBody (radix : ℕ) : Stmt :=
  .set 12 (M (v 2 -' k 9)) ;;
  .set 13 (M (v 2 -' k 8)) ;;
  .set 14 (M (v 2 -' k 7)) ;;
  .set 15 (M (v 2 -' k 5)) ;;
  .set 16 (M (v 2 -' k 3)) ;;
  .set 17 (M (v 2) +' k 1) ;;
  .set 18 (v 4 +' k 100 *' (v 1 +' v 17 +' k 1)) ;;
  .set 19 (v 18 +' k 19) ;;
  .set 20 (v 19 +' v 9 *' (v 14 +' k 2)) ;;
  .call 37 [k 2,v 14] 22 ;;
  .set 23 (v 7 *' v 22) ;;
  .set 25 (v 20 +' v 11 *' (v 14 +' k 2)) ;;
  .set 24 (v 25 +' v 22 *' (v 14 +' k 1)) ;;
  .set 21 (v 24 +' v 23) ;;
  .set 26 (v 21 +' v 23 *' (v 14 +' k 2)) ;;
  .set 27 (v 26 +' k 100 *' (v 12 +' v 22 +' v 14 +' k 1)) ;;
  .call 28 [v 8,v 9,v 12,v 14,k radix,v 19,v 26] 28 ;;
  .call 32 [v 10,v 11,v 12,v 14,k radix,v 20,v 26] 28 ;;
  .call 36 [v 14,v 25,v 26] 28 ;;
  .call 49 [v 6,v 7,v 12,v 14,k radix,v 25,v 22,v 24,v 21,v 26] 28 ;;
  stores 0 fields ;;
  .set 0 (v 18)
def body (radix : ℕ) : Stmt :=
  .call 27 [v 0,v 1,v 2,v 3,v 4] 5 ;;
  .set 6 (M (v 5)) ;; .set 7 (M (v 5 +' k 1)) ;;
  .set 8 (M (v 5 +' k 2)) ;; .set 9 (M (v 5 +' k 3)) ;;
  .set 10 (M (v 5 +' k 4)) ;; .set 11 (M (v 5 +' k 5)) ;;
  .ite (v 7 =' k 0) (.set 0 (k 0))
    (.ite (v 9 =' k 0) (.set 0 (k 0))
      (.ite (v 11 =' k 0) (.set 0 (k 0)) (buildBody radix)))
def program (radix : ℕ) : Program :=libraries++[body radix]
def headerAt (free n W : ℕ) :=free+100*(n+W+1)
def bMatrix (free n W : ℕ) :=headerAt free n W+19
def cMatrix (free n W nB J : ℕ) :=bMatrix free n W+nB*(J+2)
def carry (free n W nA nB nC J : ℕ) :=cMatrix free n W nB J+nC*(J+2)
def positions (free n W nA nB nC J : ℕ) :=carry free n W nA nB nC J+2^J*(J+1)
def oMatrix (free n W nA nB nC J : ℕ) :=positions free n W nA nB nC J+nA*2^J
def work (free n W nA nB nC J : ℕ) :=oMatrix free n W nA nB nC J+nA*2^J*(J+2)
def arenaFree (free n W nA nB nC J U : ℕ) :=work free n W nA nB nC J+100*(U+2^J+J+1)
end ThreeSum.LightWeightedGlobalColorPreparation
end WeightedCache3SUMRefinement_e1ae71d


