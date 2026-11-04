-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixExplicit
-- name    : Submission_ThreeSum_LightReportingSuffixExplicit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:26:29.025088+00:00
-- url     : https://prove2.me/theorems/8fd01ffa-9ff8-417e-ae78-388a81c1055a
-- title:
--   Light Reporting Suffix Explicit
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Explicit, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixExplicit.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSum
import Definitions.Def_Submission_ThreeSum_LightExplicitSum
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixExplicit
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostSuffix
variable {lim : Limits} {P : Program}
structure Procs (P : Program) (pEnum pSum : ℕ) where
  (pWeights pCore pLeaf pAddress : ℕ)
  leafProcs : LightSignedLeafCell.Procs P pLeaf pAddress
  enumerate : P[pEnum]? = some (LightQueryEnumeration.body pWeights pCore)
  weights : P[pWeights]? = some (LightQueryWeights.body leafProcs.pPowers leafProcs.pErase)
  core : P[pCore]? = some (LightSubsetEnumeration.body pCore)
  sum : P[pSum]? = some (LightReportingSuffixSum.body pLeaf)
def roundBody (pEnum pSum : ℕ) : Stmt :=
  .call pEnum [v 7,v 10,v 17,v 14,v 15] 18 ;;
  .call pSum [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 17,v 18,v 14,v 12,v 13,v 15] 19 ;;
  .set 16 (v 16 +' v 19)
def body (pEnum pSum : ℕ) : Stmt :=
  .set 16 (k 0) ;;
  .for 17 (v 11) (roundBody pEnum pSum) ;;
  .set 0 (v 16)
def roundTime (W c t : ℕ) : ℕ := 10500*(W+1)^2*(layerOffset c t+1)
def time (W c t : ℕ) : ℕ := t*(roundTime W c t+30)+40
def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage cut t baseL baseR maskBase work j : ℕ) (σ : State) : Prop :=
  ∃ (count r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,V,2^offset,
      Q.card,subsetMask Q,t,baseL,baseR,maskBase,work,
      ExplicitLayers.valueSum Q (leafWeight hfit f g stage preL preR) j,j,count,r],μ'⟩ ∧
      KeptBut μ μ' work maskBase (layerOffset Q.card t)
end ThreeSum.LightReportingSuffixExplicit


