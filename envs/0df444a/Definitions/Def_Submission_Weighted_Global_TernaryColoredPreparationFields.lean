-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredPreparationFields
-- name    : Submission_Weighted_Global_TernaryColoredPreparationFields
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:09:42.643264+00:00
-- url     : https://prove2.me/theorems/7a461f4b-7f70-4803-964c-864d3ab167ac
-- title:
--   Ternary Colored Preparation Fields
-- statement:
--   Definitions and structural lemmas for Ternary Colored Preparation Fields, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationFields.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredInitializationProof
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredPreparationFields
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000
variable {κ : ℕ}
def fields (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) : List ℕ :=
  let J:=J P n
  let W:=LightColorParametersCosts.width n
  [LightTernaryColorPrelude.av free n,A.length,LightTernaryColorPrelude.bv free n,B.length,
    LightTernaryColorPrelude.cv free n,C.length,bMatrix free n W,cMatrix free n W B.length J,
    oMatrix free n W A.length B.length C.length J,A.length*2^J,
    positions free n W A.length B.length C.length J,carry free n W A.length B.length C.length J,
    work free n W A.length B.length C.length J,
    arenaFree free n W A.length B.length C.length J (n^κ),n^κ,rounds P n,J,q P n,menu]
def field (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) (i : ℕ) :=
  (fields P n free menu A B C).getD i 0
end ThreeSum.WeightedGlobalColoredPreparationFields


