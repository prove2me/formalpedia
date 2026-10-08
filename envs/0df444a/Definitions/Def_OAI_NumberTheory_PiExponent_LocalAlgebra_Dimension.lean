-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_Dimension
-- name    : OAI_NumberTheory_PiExponent_LocalAlgebra_Dimension
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T13:26:59.133608+00:00
-- url     : https://prove2.me/theorems/8275f04b-be5f-4321-beb8-4670cc14cfc0
-- title:
--   Auxiliary dimension scales and a floor bound
-- statement:
--   For real C and a natural number m, dimensionK C m is the natural floor of C^m; dimensionW B m is B^m inverse; and dimensionV theta B C m is 2 times dimensionK C m, theta^m, and dimensionW B m. If C is nonnegative, the real cast of dimensionK C m is at most C^m.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/Dimension.lean#L17-L26

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring






namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace PiExponent

def dimensionK (C : ℝ) (m : ℕ) : ℕ := ⌊C ^ m⌋₊

def dimensionW (B : ℝ) (m : ℕ) : ℝ := (B ^ m)⁻¹

def dimensionV (theta B C : ℝ) (m : ℕ) : ℝ :=
  2 * (dimensionK C m : ℝ) * theta ^ m * dimensionW B m

theorem dimensionK_le (C : ℝ) (hC : 0 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) ≤ C ^ m :=
  Nat.floor_le (pow_nonneg hC m)

























end PiExponent

end

end OAI


