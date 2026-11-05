-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaHeaderAgreement
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaHeaderAgreement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:52:23.70539+00:00
-- url     : https://prove2.me/theorems/9ec9ebf8-afa9-4ff6-a41c-cf9aac90f277
-- title:
--   TernaryArenaHeaderAgreement
-- statement:
--   Definitions and structural lemmas for TernaryArenaHeaderAgreement, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaHeaderAgreement.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixHeaderSegment
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRepeatWordAddress
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaHeaderAgreement
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
def templateInputs (I : Input) (p m F : ℕ) : List ℤ :=
  [0,I.free,0,I.nB,0,I.nC,0,I.requesterCount,0,0,0,0,0,p,4^(fixedLength m),F,0,0,0,0,0,0,0]
def templateValues (I : Input) (p m F : ℕ) : List ℤ :=
  LightWeightedGlobalArenaTemplate.hostValues (frame (templateInputs I p m F)) I.free I.capacity
def emittedHeader (I : Input) (p m F j : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m) (ret : ℤ) : List ℤ :=
  LightWeightedGlobalPrefixHeader.resultHeader (templateValues I p m F)
    (addr I.free I.capacity 0) (addr I.free I.capacity 1)
    (LightWeightedGlobalPrefixSetup.headerAt I.prefixFree m (j+1)) (j+1) m p (p^j)
    (fixedAlpha m 2) (alphaRank m) (TernaryCodeSemantics.address Q.val) (4^(fixedLength m)) 0
    (N m (j+1)) (cut m (j+1)) (2*N m (j+1)) (F^(j+1)) (nb m (j+1))
    I.prefixFree (I.prefixFree+4^(N m (j+1)))
    (addr I.free I.capacity 50) (addr I.free I.capacity 51) ret
end ThreeSum.WeightedGlobalArenaHeaderAgreement
end
end WeightedCache3SUMRefinement_e1ae71d


