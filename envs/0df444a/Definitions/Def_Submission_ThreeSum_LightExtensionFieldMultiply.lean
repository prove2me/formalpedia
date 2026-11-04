-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionFieldMultiply
-- name    : Submission_ThreeSum_LightExtensionFieldMultiply
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:44:48.373051+00:00
-- url     : https://prove2.me/theorems/54fe1088-a4d6-41d0-b481-a81efff13b20
-- title:
--   Light Extension Field Multiply
-- statement:
--   Definitions and structural lemmas for Light Extension Field Multiply, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFieldMultiply.lean

import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightExtensionFieldMultiply
open Light TernaryExtensionEncoding
set_option maxHeartbeats 2000000
noncomputable local instance _p2m_local_instance_74f6067cfd_8 (Q : Prop) : Decidable Q := Classical.propDecidable Q
variable {p : ℕ} [Fact p.Prime] {f : Polynomial (ZMod p)}
end ThreeSum.LightExtensionFieldMultiply


