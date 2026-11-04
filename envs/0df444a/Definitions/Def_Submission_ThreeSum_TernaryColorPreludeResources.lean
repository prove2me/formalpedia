-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources
-- name    : Submission_ThreeSum_TernaryColorPreludeResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:41:04.864771+00:00
-- url     : https://prove2.me/theorems/097e66a5-6774-4c73-b0d0-ef3f975b9db0
-- title:
--   Ternary Color Prelude Resources
-- statement:
--   Definitions and structural lemmas for Ternary Color Prelude Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryColorPreludeResources.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
set_option autoImplicit false
namespace ThreeSum.TernaryColorPreludeResources
open Light LightTernaryColorPrelude LightColorParametersCosts StageBounds
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
def need (n U : ℕ) : Light.Need :=
  ⟨word n U,14*n+width n+20,2*width n+n+20⟩
noncomputable section
end
end ThreeSum.TernaryColorPreludeResources


