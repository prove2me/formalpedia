-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoTruncate_F001
-- name    : LevyStochCalc_Brownian_ItoTruncate_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:43:06.46234+00:00
-- url     : https://prove2.me/theorems/af259e7a-f311-4ff5-b2ee-2fd2888103e8
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoTruncate
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoTruncate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F001
import Definitions.Def_LevyStochCalc_Brownian_VectorItoVersionExists_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncating an integrand to a bounded one

Clamping a real integrand to `[-j, j]` leaves a bounded integrand that approximates it in energy:
the clamp is `1`-Lipschitz, fixes `0`, never increases the absolute value, and converges to the
identity pointwise, so dominated convergence gives energy convergence on every window.

## Main statements

* `LevyStochCalc.clampAt` — the clamp.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_clampAt_sub` — the clamped integrand converges to
  the integrand in energy.
-/

namespace LevyStochCalc

open MeasureTheory
open scoped NNReal ENNReal Topology

section Clamp

end Clamp

namespace Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Difference

open LevyStochCalc.Brownian.Multidim

variable {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

/-- The squared norm of a real vector is at most the sum of its squared coordinates, in `ℝ≥0∞`. -/
theorem sq_enorm_pi_le_sum {m : ℕ} (x : Fin m → ℝ) :
    (‖x‖₊ : ℝ≥0∞) ^ 2 ≤ ∑ p, (‖x p‖₊ : ℝ≥0∞) ^ 2 := by
  have hnn : ‖x‖₊ ^ 2 ≤ ∑ p, ‖x p‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    simpa [Real.norm_eq_abs, sq_abs] using sq_norm_pi_le_sum_sq x
  calc (‖x‖₊ : ℝ≥0∞) ^ 2 = ((‖x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((∑ p, ‖x p‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hnn
    _ = ∑ p, (‖x p‖₊ : ℝ≥0∞) ^ 2 := by push_cast; ring
end Difference

end Brownian.Ito

end LevyStochCalc


