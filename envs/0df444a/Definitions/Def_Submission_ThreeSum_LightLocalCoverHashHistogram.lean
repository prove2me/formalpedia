-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverHashHistogram
-- name    : Submission_ThreeSum_LightLocalCoverHashHistogram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:46:16.355817+00:00
-- url     : https://prove2.me/theorems/b681cbf5-2d2a-4a9d-8443-98c945515be2
-- title:
--   Light Local Cover Hash Histogram
-- statement:
--   Definitions and structural lemmas for Light Local Cover Hash Histogram, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverHashHistogram.lean

import Definitions.Def_Submission_ThreeSum_LightHashHistogram
set_option autoImplicit false
namespace ThreeSum.LightLocalCoverHashHistogram
open Light LightHashHistogram
def Preserved (μ ν : ℕ → ℤ) (work raw codes hist n p : ℕ) : Prop :=
  ∀ a, a < work → Outside raw n a → Outside codes n a → Outside hist p a → ν a = μ a
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightLocalCoverHashHistogram


