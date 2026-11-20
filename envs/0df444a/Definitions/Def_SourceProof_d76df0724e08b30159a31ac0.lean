-- Prove2me | Definitions.Def_SourceProof_d76df0724e08b30159a31ac0
-- name    : SourceProof_d76df0724e08b30159a31ac0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T10:59:00.329635+00:00
-- url     : https://prove2.me/theorems/7f91b634-5d6d-4023-bcdf-7b6b60bb49a4
-- title:
--   LevyStochCalc source module: SourceProof_d76df0724e08b30159a31ac0
-- statement:
--   The original source theorem `LevyStochCalc.Probability.sq_sum_le_card_sq_mul` comes from the `LevyStochCalc.Probability.DoobContinuous` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F000
import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F001
import Definitions.Def_MathFin_Foundations_DoobLpMaximalInequality_F000
import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob's `L²` maximal inequality in continuous time

For a right-continuous martingale on `[0, T]`, the supremum of the paths over the window is
square integrable, with `𝔼[sup_{t ≤ T} |M_t|²] ≤ 4 𝔼[|M_T|²]`.

The discrete inequality is `MeasureTheory.Martingale.eLpNorm_norm_runMax_le`; the passage to
continuous time samples the martingale along the dyadic partition of `[0, T]`, whose points are
increasing in the level, and uses right-continuity to identify the supremum over the window with
the supremum of the sampled maxima.

## Main statements

* `Filtration.compMono`, `martingale_compMono` — sampling along a monotone time map.
* `dyadicTime` — the dyadic partition points of `[0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Sampling along a monotone time map -/

/-! ### The dyadic partition of `[0, T]` -/

/-! ### The sampled running maxima -/

variable {M : ℝ → Ω → ℝ} {T : ℝ}

/-! ### The supremum over the window -/

/-! ### Doob's `L²` inequality in continuous time -/

/-! ### Bounding the supremum over the window -/

/-! ### Finite sums -/


theorem _root_.Prove2MeSourceProof.h_d76df0724e08b30159a31ac0 {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) ^ 2 * ∑ i ∈ s, f i ^ 2 := by
  have h1 : ∑ i ∈ s, f i ≤ (s.card : ℝ≥0∞) * s.sup f := by
    calc ∑ i ∈ s, f i ≤ ∑ _i ∈ s, s.sup f :=
          Finset.sum_le_sum fun i hi => Finset.le_sup hi
      _ = (s.card : ℝ≥0∞) * s.sup f := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : s.sup f ^ 2 ≤ ∑ i ∈ s, f i ^ 2 := by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_sup s hne f
      rw [hieq]
      exact Finset.single_le_sum (f := fun j => f j ^ 2) (fun _ _ => zero_le) hi
  calc (∑ i ∈ s, f i) ^ 2 ≤ ((s.card : ℝ≥0∞) * s.sup f) ^ 2 := pow_le_pow_left' h1 2
    _ = (s.card : ℝ≥0∞) ^ 2 * s.sup f ^ 2 := by rw [mul_pow]
    _ ≤ (s.card : ℝ≥0∞) ^ 2 * ∑ i ∈ s, f i ^ 2 := mul_le_mul' le_rfl h2
end LevyStochCalc.Probability


