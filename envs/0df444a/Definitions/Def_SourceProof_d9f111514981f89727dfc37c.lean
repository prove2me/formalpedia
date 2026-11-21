-- Prove2me | Definitions.Def_SourceProof_d9f111514981f89727dfc37c
-- name    : SourceProof_d9f111514981f89727dfc37c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:01:35.067183+00:00
-- url     : https://prove2.me/theorems/9def7297-4366-4e97-91a1-b1e7867e8974
-- title:
--   LevyStochCalc source module: SourceProof_d9f111514981f89727dfc37c
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.lintegral_energy_sub_le` comes from the `LevyStochCalc.Ito.VectorItoVersionSup` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_VectorItoProcessDiff_F000
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The window supremum of the difference of two vector Itô versions

Two versions driven by different coefficients differ by a drift part, controlled pathwise by
Cauchy–Schwarz, and a martingale part, controlled by Doob's `L²` maximal inequality. Sampling the
paths on the dyadic points of the window turns the supremum into a countable one, which is all the
maximal inequality needs.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le` — the second moment of the
  window supremum of the difference, in terms of the coefficients' energies.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Helpers

variable {Ω : Type u}

variable [MeasurableSpace Ω] {P : Measure Ω}

end Helpers

section SupBound

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_d9f111514981f89727dfc37c {f g h : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hh : Measurable (Function.uncurry h)) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s - g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
  have hptw : ∀ (ω : Ω) (s : ℝ), (‖f ω s - g ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 + (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s
    have hb := LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul (f ω s - h ω s) (g ω s - h ω s)
    simpa [sub_sub_sub_cancel_right] using hb
  have hmfh : Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := LevyStochCalc.Brownian.Ito.measurable_energyDensity (hf.sub hh) T
  have hmgh : Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := LevyStochCalc.Brownian.Ito.measurable_energyDensity (hg.sub hh) T
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s - g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          2 * ((‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2
            + (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω => MeasureTheory.lintegral_mono fun s => hptw ω s
    _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
        have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            2 * ((‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2
              + (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume
            = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) := by
          intro ω
          have hfhm : Measurable fun s : ℝ => (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 := by
            have h1 : Measurable fun s : ℝ => f ω s - h ω s :=
              (Measurable.of_uncurry_left hf).sub (Measurable.of_uncurry_left hh)
            exact ((h1.nnnorm).coe_nnreal_ennreal).pow_const 2
          rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
            MeasureTheory.lintegral_add_left hfhm]
        simp only [hinner]
        rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
          MeasureTheory.lintegral_add_left hmfh]
end SupBound

end LevyStochCalc.Brownian.Ito


