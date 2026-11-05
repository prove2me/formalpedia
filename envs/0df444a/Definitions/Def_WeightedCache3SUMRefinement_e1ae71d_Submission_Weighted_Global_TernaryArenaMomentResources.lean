-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaMomentResources
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaMomentResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:26:39.328561+00:00
-- url     : https://prove2.me/theorems/0d306f33-ec81-4ea5-b27a-5a651a44a8b7
-- title:
--   TernaryArenaMomentResources
-- statement:
--   Definitions and structural lemmas for TernaryArenaMomentResources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaMomentResources.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaReporterBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryModel
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


