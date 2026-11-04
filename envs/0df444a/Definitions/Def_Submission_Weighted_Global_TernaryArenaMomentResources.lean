-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
-- name    : Submission_Weighted_Global_TernaryArenaMomentResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:36:20.622194+00:00
-- url     : https://prove2.me/theorems/62a79577-403e-450d-98cd-0e1cb373c647
-- title:
--   Ternary Arena Moment Resources
-- statement:
--   Definitions and structural lemmas for Ternary Arena Moment Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaMomentResources.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaMomentResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPairMass
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeMomentBounds
open WeightedGlobalMomentWeightBounds
variable {p m F r : ℕ} [Fact p.Prime]
def detectorNeed (maps : Fin F→Weight m p) (cap M H n U : ℕ) : Need :=
  WeightedGlobalMomentDetectorResources.need (envelope maps cap M n) U H
def channelNeed (maps : Fin F→Weight m p) (cap M H n U : ℕ) : Need :=
  WeightedGlobalMomentChannelResources.need (envelope maps cap M n) U (2*H)
end ThreeSum.WeightedGlobalArenaMomentResources


