-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPreparationFields
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPreparationFields
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:05:45.702554+00:00
-- url     : https://prove2.me/theorems/4db87c21-b2b3-436b-8aff-00cd6383b8f4
-- title:
--   TernaryColoredPreparationFields
-- statement:
--   Definitions and structural lemmas for TernaryColoredPreparationFields, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPreparationFields.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredInitializationProof
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


