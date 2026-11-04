-- Prove2me | Definitions.Def_Submission_ThreeSum_PrimeDensity
-- name    : Submission_ThreeSum_PrimeDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:38.258802+00:00
-- url     : https://prove2.me/theorems/f2339e3e-e6f0-4842-a6d9-dd14901b84da
-- title:
--   Prime Density
-- statement:
--   Definitions and structural lemmas for Prime Density, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeDensity.lean

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Mathlib.NumberTheory.Chebyshev
set_option autoImplicit false
namespace ThreeSum.PrimeDensity
open Real Filter Finset
open scoped Topology
def candidates (y : ℕ) : Finset ℕ := Nat.primesLE (4 * y) \ Nat.primesLE y
noncomputable section
def lowerScaled (y : ℕ) : ℝ :=
  (4 * Real.log 2 - Real.log (4 * y + 1 : ℝ) / y) /
    (1 + Real.log 4 / Real.log y)
end
end ThreeSum.PrimeDensity


