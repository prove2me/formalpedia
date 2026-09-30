-- Prove2me | Definitions.Def_TauCeti_NumberTheory_AbelSummation
-- name    : TauCeti_NumberTheory_AbelSummation
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:36:51.823707+00:00
-- url     : https://prove2.me/theorems/f2bff272-0529-4de1-9de3-4b6d82d85940
-- title:
--   Consequences of Abel summation for partial sums
-- statement:
--   For real $t$, set
--
--   $$
--   w(t)=\frac1{t(1+\log t)^3}.
--   $$
--
--   This is the smoothing weight used in partial summation of sequences with logarithmic growth.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/AbelSummation.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/AbelSummation.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Consequences of Abel summation for partial sums

Mathlib's `Mathlib/NumberTheory/AbelSummation.lean` proves the summation-by-parts identity
`∑_{k ≤ x} f k c k = f x ∑_{k ≤ x} c k - ∫ f' (t) ∑_{k ≤ t} c k dt` and derives convergence
criteria from it. This file draws two further consequences from a growth hypothesis on the
partial sums `∑_{1 ≤ k ≤ t} c k`.

* **A logarithmic weight.** Mathlib's `summable_mul_of_bigO_atTop'` converts a bound on the partial
  sums of a sequence into the convergence of a weighted series, provided the weight is
  differentiable and the derivative of the weight against the partial sums admits an integrable
  majorant. This file performs that conversion once, for the weight `(t (1 + log t) ^ 3)⁻¹` and
  partial sums growing like `t log t`. The weight is written with `1 + log t` rather than `log t`
  so that it stays positive and smooth at `t = 1`, where Abel summation starts. Its derivative
  against an `O(t log t)` partial sum is `O((t (1 + log t) ^ 2)⁻¹)`, which is integrable at
  infinity by comparison with Mathlib's log-Cauchy density
  `integrableOn_Ioi_zero_inv_mul_one_add_log_sq`.
* **A power weight.** If the partial sums grow like `κ x`, then the partial sums weighted by
  `n ^ τ`, for an exponent `τ > -1`, grow like `κ x ^ (τ + 1) / (τ + 1)`. This is the step that
  moves a Tauberian conclusion for the coefficients `a n n ^ (1 - σ)` back to the coefficients
  `a n`.

## Main declarations

* `TauCeti.summable_div_mul_one_add_log_cube`: if the partial sums `∑_{1 ≤ k ≤ t} u k` of a
  nonnegative sequence are `O(t log t)`, then `∑ u n / (n (1 + log n) ^ 3)` converges.
* `TauCeti.sum_Icc_rpow_mul_eq`: the exact Abel-summation identity for the weight `t ^ τ`.
* `TauCeti.tendsto_rpow_inv_mul_sum_Icc_rpow_mul`: if `x⁻¹ ∑_{1 ≤ n ≤ x} c n → κ`, then
  `(x ^ (τ + 1))⁻¹ ∑_{1 ≤ n ≤ x} n ^ τ c n → κ / (τ + 1)` for `τ > -1`.
-/

 section

namespace TauCeti

open Asymptotics Filter MeasureTheory Set
open scoped Topology

variable {t : ℝ}

/-! ### The comparison weight -/

/-- The weight `(t (1 + log t) ^ 3)⁻¹` against which a partial-sum bound is summed. -/
 noncomputable def decayWeight (t : ℝ) : ℝ := (t * (1 + Real.log t) ^ 3)⁻¹

















/-! ### The hypotheses of Abel summation -/





/-! ### The weighted series -/



/-! ### Partial sums against a power weight -/







end TauCeti

end
end


