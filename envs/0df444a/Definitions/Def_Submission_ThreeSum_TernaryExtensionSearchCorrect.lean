-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
-- name    : Submission_ThreeSum_TernaryExtensionSearchCorrect
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:38:28.240846+00:00
-- url     : https://prove2.me/theorems/26fbcea9-0a4d-4282-8267-e8ba256fa740
-- title:
--   Ternary Extension Search Correct
-- statement:
--   Definitions and structural lemmas for Ternary Extension Search Correct, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSearchCorrect.lean

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
end ThreeSum.TernaryExtensionEncoding


