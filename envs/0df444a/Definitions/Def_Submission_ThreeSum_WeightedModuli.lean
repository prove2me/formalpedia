-- Prove2me | Definitions.Def_Submission_ThreeSum_WeightedModuli
-- name    : Submission_ThreeSum_WeightedModuli
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:54:07.82932+00:00
-- url     : https://prove2.me/theorems/55fc9f6a-e92c-4e41-b238-d2ee607fb7ee
-- title:
--   Weighted Moduli
-- statement:
--   Definitions and structural lemmas for Weighted Moduli, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedModuli.lean

import Definitions.Def_Submission_ThreeSum_Auxiliary
set_option autoImplicit false
namespace ThreeSum.WeightedModuli
open Finset Arithmetic
open scoped BigOperators
def joint (q p : ℕ) : ℕ := if p ∣ q then q else q * p
end ThreeSum.WeightedModuli


