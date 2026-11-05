-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceCertificate
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:05:54.691225+00:00
-- url     : https://prove2.me/theorems/3d453a8e-0d2d-440c-9489-d7b9a6918a0f
-- title:
--   TernaryArenaSourceCertificate
-- statement:
--   Definitions and structural lemmas for TernaryArenaSourceCertificate, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceCertificate.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceModel
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSourceCertificate
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
open LightTernarySourceHost TernaryCodeSemantics
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
end ThreeSum.WeightedGlobalArenaSourceCertificate
end
end WeightedCache3SUMRefinement_e1ae71d


