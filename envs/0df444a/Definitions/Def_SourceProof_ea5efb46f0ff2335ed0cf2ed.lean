-- Prove2me | Definitions.Def_SourceProof_ea5efb46f0ff2335ed0cf2ed
-- name    : SourceProof_ea5efb46f0ff2335ed0cf2ed
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:42:51.293151+00:00
-- url     : https://prove2.me/theorems/809fe49d-7f86-49d6-af9c-acc38b88a761
-- title:
--   LevyStochCalc source module: SourceProof_ea5efb46f0ff2335ed0cf2ed
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.sq_enorm_finsetSum_le` comes from the `LevyStochCalc.Brownian.ItoTruncate` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_ea5efb46f0ff2335ed0cf2ed {m : ℕ} (x : Fin m → ℝ) :
    (‖∑ k, x k‖₊ : ℝ≥0∞) ^ 2 ≤ (m : ℝ≥0∞) * ∑ k, (‖x k‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : (∑ k, |x k|) ^ 2 ≤ (m : ℝ) * ∑ k, |x k| ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m))) (f := fun k => |x k|)
    simpa using this
  have habs : |∑ k, x k| ≤ ∑ k, |x k| := Finset.abs_sum_le_sum_abs _ _
  have hnn : ‖∑ k, x k‖₊ ^ 2 ≤ (m : ℝ≥0) * ∑ k, ‖x k‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    have h1 : |∑ k, x k| ^ 2 ≤ (∑ k, |x k|) ^ 2 := by
      have h0 : (0 : ℝ) ≤ |∑ k, x k| := abs_nonneg _
      nlinarith [habs, h0]
    calc |∑ k, x k| ^ 2 ≤ (∑ k, |x k|) ^ 2 := h1
      _ ≤ (m : ℝ) * ∑ k, |x k| ^ 2 := hreal
      _ = (m : ℝ) * ∑ k, |x k| ^ 2 := rfl
  calc (‖∑ k, x k‖₊ : ℝ≥0∞) ^ 2 = ((‖∑ k, x k‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ (((m : ℝ≥0) * ∑ k, ‖x k‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hnn
    _ = (m : ℝ≥0∞) * ∑ k, (‖x k‖₊ : ℝ≥0∞) ^ 2 := by push_cast; ring
end Difference

end Brownian.Ito

end LevyStochCalc


