-- Prove2me | Definitions.Def_SourceProof_e4a003adac246e81fe5cee0f
-- name    : SourceProof_e4a003adac246e81fe5cee0f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:13:06.712144+00:00
-- url     : https://prove2.me/theorems/0ba6e96e-50a1-46c9-9278-1e9d766ca214
-- title:
--   LevyStochCalc source module: SourceProof_e4a003adac246e81fe5cee0f
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul_brownian` comes from the `LevyStochCalc.Brownian.ItoDensityDyadicAverages` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F002
import Definitions.Def_LevyStochCalc_Probability_Progressive_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncation in `L²` and dyadic cell averages

Truncation of an `L²(Ω × [0,T])` integrand at level `M` together with the `L²` error it
incurs, the dyadic partition of `[0,T]`, the cell averages of an integrand over the
partition intervals, and the simple predictable process whose values on the `n`-th dyadic
grid are those averages.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_e4a003adac246e81fe5cee0f (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  have h_norm_sq : ∀ z : ℝ, (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) :=
    fun z => by
    rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from ofReal_norm z |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖z‖ ^ 2 = z ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
  rw [h_norm_sq, h_norm_sq, h_norm_sq]
  have h_real : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have h_nn_x : 0 ≤ x ^ 2 := sq_nonneg _
  have h_nn_y : 0 ≤ y ^ 2 := sq_nonneg _
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat]]
  rw [← ENNReal.ofReal_add h_nn_x h_nn_y, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact ENNReal.ofReal_le_ofReal h_real
-- `omit` the unused `[MeasurableSpace Ω]` section variable (this lemma's
-- `g : Ω → ℝ → ℝ` does not need it).

end LevyStochCalc.Brownian.Ito


