-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
-- name    : Submission_Weighted_Global_LightTernarySeedScore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:15:59.488469+00:00
-- url     : https://prove2.me/theorems/8a485fc3-996c-4c0e-8bd6-5fe5605f2ffd
-- title:
--   Light Ternary Seed Score
-- statement:
--   Definitions and structural lemmas for Light Ternary Seed Score, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScore.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriver
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalSeedScore
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
def body : Stmt :=
  .set 40 (v 2 +' k 2) ;;
  .set 41 (v 0 +' v 1 *' v 40) ;;
  .call 6 [v 3,v 4,v 2,v 41] 42 ;;
  .call 14 [v 7,v 41,v 8,v 9,v 10,v 40,v 5,v 6,v 22] 48 ;;
  .call 14 [v 11,v 41,v 12,v 13,v 14,v 40,v 5,v 6,v 22] 48 ;;
  .call 14 [v 15,v 41,v 16,v 17,v 18,v 40,v 5,v 6,v 22] 48 ;;
  .call 19 [v 39,v 17,v 19,v 18,v 20,v 21] 43 ;;
  .call 24 [v 43 -' v 20,k 3] 44 ;;
  .call 20 [v 9,v 10,v 23,v 6 *' v 5] 45 ;;
  .call 20 [v 13,v 14,v 23,v 6 *' v 5] 46 ;;
  .store (v 24 +' k 104) (v 44) ;;
  .call (25+LightWeightedGlobalTensorDriver.entry) [v 24,v 25,v 10,v 26,v 14,v 2,v 27,v 28,v 29,v 44,v 30,
    v 31,v 32,v 33,v 34] 47 ;;
  .store (v 35 +' v 1) (v 42) ;;
  .store (v 36 +' v 1) (v 45) ;;
  .store (v 37 +' v 1) (v 46) ;;
  .store (v 38 +' v 1) (v 47) ;;
  .set 0 (v 42)
def spanAppend : Program := ReportingHostRelocation.program
  LightStoredSpan.program LightTernaryAppendKeys.program
def withWanted (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : Program :=
  ReportingHostRelocation.program spanAppend
    (LightTernaryWantedBatch.program p R S raws words maps)
def withCollision (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : Program :=
  ReportingHostRelocation.program (withWanted p R S raws words maps)
    LightOriginalCollisionScore.program
def withDivision (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : Program :=
  ReportingHostRelocation.program (withCollision p R S raws words maps) LightSmallDivide.program
def libraries (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) : Program :=
  ReportingHostRelocation.program (withDivision p R S raws words maps)
    (LightWeightedGlobalTensorDriver.program xl yl zl xr yr zr K)
def program (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) : Program :=
  libraries p R S K raws words maps xl yl zl xr yr zr++[body]
def time (TS TB TC TO TW TD XB XC TP : ℕ) : ℕ :=
  TS+TB+TC+TO+TW+TD+XB+XC+TP+1000
def args (menu seed J catalog catalogRows p power Bmatrix Bold Bnew nB
    Cmatrix Cold Cnew nC Omatrix Oold Onew nO positions wanted work hashWork hist
    header leftTagged rightTagged leftWeights rightWeights tensor countOutput quadScratch
    quadPowers potentialColumns potentialPowers flags scoreB scoreC scorePaired prefixLength : ℕ) : List ℤ :=
  [menu,seed,J,catalog,catalogRows,p,power,Bmatrix,Bold,Bnew,nB,Cmatrix,Cold,Cnew,nC,
    Omatrix,Oold,Onew,nO,positions,wanted,work,hashWork,hist,header,leftTagged,rightTagged,
    leftWeights,rightWeights,tensor,countOutput,quadScratch,quadPowers,potentialColumns,
    potentialPowers,flags,scoreB,scoreC,scorePaired,prefixLength]
section Lift
variable {lim : Limits} {entry depth T : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
  {Post : ℤ → (ℕ → ℤ) → Prop}
end Lift
def entry : ℕ := 176
end ThreeSum.LightWeightedGlobalSeedScore


