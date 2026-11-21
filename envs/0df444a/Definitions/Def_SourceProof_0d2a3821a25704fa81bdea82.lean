-- Prove2me | Definitions.Def_SourceProof_0d2a3821a25704fa81bdea82
-- name    : SourceProof_0d2a3821a25704fa81bdea82
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:52:30.095979+00:00
-- url     : https://prove2.me/theorems/f9ca1ded-2686-4a44-92db-b6d573961c1e
-- title:
--   LevyStochCalc source module: SourceProof_0d2a3821a25704fa81bdea82
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.lintegral_sq_indIoc_lt_top` comes from the `LevyStochCalc.Brownian.ItoIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô integral of an indicator is a Brownian increment

The integrand `1_{(a, b]}` is simple, so its `L²` Itô integral up to a time `t` is the elementary
integral `W_{b ∧ t} − W_{a ∧ t}`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Indicator

theorem _root_.Prove2MeSourceProof.h_0d2a3821a25704fa81bdea82 (P : Measure Ω) [IsProbabilityMeasure P] (a b : ℝ)
    (T : ℝ) (_hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ (ω : Ω) (s : ℝ), (‖LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ≤ 1 := by
    intro ω s
    have hx : ‖LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s‖ ≤ 1 := (Real.norm_eq_abs _).le.trans (LevyStochCalc.Brownian.Ito.indIoc_le_one a b ω s)
    have : (‖LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s‖₊ : ℝ≥0∞) ≤ 1 := by
      rw [← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
      simpa using hx
    simpa using pow_le_pow_left' this 2
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ : Ω, ∫⁻ _ in Set.Icc (0 : ℝ) T, (1 : ℝ≥0∞) ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ < ⊤ := by
        simp only [lintegral_one, Measure.restrict_apply_univ, Real.volume_Icc,
          lintegral_const, measure_univ, mul_one]
        exact ENNReal.ofReal_lt_top
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end Indicator

end LevyStochCalc.Brownian.Ito


