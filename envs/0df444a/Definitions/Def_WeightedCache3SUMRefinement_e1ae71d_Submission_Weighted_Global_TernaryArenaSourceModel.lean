-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceModel
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:03:52.777523+00:00
-- url     : https://prove2.me/theorems/59efa4e3-3eae-40c4-953e-741c1814fc7b
-- title:
--   TernaryArenaSourceModel
-- statement:
--   Definitions and structural lemmas for TernaryArenaSourceModel, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceModel.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalSourceBank
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSourceModel
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
abbrev Index (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) :=
  Fin ((localRecords maps cap right).length^r)
end ThreeSum.WeightedGlobalArenaSourceModel
end
end WeightedCache3SUMRefinement_e1ae71d


