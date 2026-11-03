-- Prove2me | Definitions.Def_levy_foundations_ceilApprox
-- name    : levy_foundations_ceilApprox
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T20:48:54.474677+00:00
-- url     : https://prove2.me/theorems/ca88e66e-d27f-4bcf-bc40-43949303cc5b
-- title:
--   Ceiling approximation of nonnegative time by rational times
-- statement:
--   For nonnegative real t and natural m, take the ceiling of t times m+1 and divide by m+1. These rational values approach t from above and support right-continuity extension arguments.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L128

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Order.Basic

open scoped NNReal Nat

namespace LevyFoundations.DensityExtension
/-- Rational ceiling approximation converging to nonnegative time from above. -/
noncomputable def ceilApprox (t : ℝ≥0) (m : ℕ) : ℝ≥0 :=
  (⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
end LevyFoundations.DensityExtension


