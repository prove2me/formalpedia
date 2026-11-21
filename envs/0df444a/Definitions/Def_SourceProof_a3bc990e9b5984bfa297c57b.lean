-- Prove2me | Definitions.Def_SourceProof_a3bc990e9b5984bfa297c57b
-- name    : SourceProof_a3bc990e9b5984bfa297c57b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:27:07.64549+00:00
-- url     : https://prove2.me/theorems/fc845b87-db93-42eb-bd9a-33f684220d38
-- title:
--   LevyStochCalc source module: SourceProof_a3bc990e9b5984bfa297c57b
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le` comes from the `LevyStochCalc.Brownian.PolarisedQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PolarisedQuadVar_F000
import Definitions.Def_SourceProof_0b802c6f1a6489d52336dde1
import Definitions.Def_SourceProof_7da1a76f350677d07bda7687

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The polarised quadratic variation

For two integrands against the *same* Brownian motion, the product of the increments of their
Itô integrals, compensated by the window integral of the product of the integrands, is
conditionally centred at the left endpoint. The identity `2xy = (x+y)² − x² − y²` reduces this
to the compensated square increments of `H₁ + H₂`, of `H₁` and of `H₂`, using additivity of the
Itô integral in the integrand.

## Main statements

* `LevyStochCalc.Brownian.Ito.polarQuadVarIncrement` — the compensated product of increments.
* `LevyStochCalc.Brownian.Ito.smul_two_polarQuadVarIncrement_ae` — the polarisation identity.
* `LevyStochCalc.Brownian.Ito.condExp_polarQuadVarIncrement` — it is conditionally centred at
  the left endpoint.
* `LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le` — its second moment.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Polarised

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H₁ H₂ : Ω → ℝ → ℝ)
  (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
  (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
  (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
  (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
  (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
  (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

section Bounds

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH₁ : ∀ ω s, |H₁ ω s| ≤ C) (hCH₂ : ∀ ω s, |H₂ ω s| ≤ C)

include hℱ hma hpa hqa hC0 hCH₁ hCH₂ in

theorem _root_.Prove2MeSourceProof.h_a3bc990e9b5984bfa297c57b {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Integrable (fun ω =>
        (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2) P
      ∧ ∫ ω, (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2 ∂P
        ≤ 3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4) * (b - a) ^ 2 := by
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  have hb₁ : ∀ ω s, |H₁ ω s| ≤ 2 * C := fun ω s => (hCH₁ ω s).trans (by linarith)
  have hb₂ : ∀ ω s, |H₂ ω s| ≤ 2 * C := fun ω s => (hCH₂ ω s).trans (by linarith)
  have hba : ∀ ω s, |H₁ ω s + H₂ ω s| ≤ 2 * C := fun ω s =>
    (abs_add_le _ _).trans (by linarith [hCH₁ ω s, hCH₂ ω s])
  have mAdd := LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab
  have m₁ := LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab
  have m₂ := LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab
  have lAdd := _root_.Prove2MeSourceProof.h_7da1a76f350677d07bda7687 W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab
  have l₁ := _root_.Prove2MeSourceProof.h_7da1a76f350677d07bda7687 W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab
  have l₂ := _root_.Prove2MeSourceProof.h_7da1a76f350677d07bda7687 W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab
  have hmp := _root_.Prove2MeSourceProof.h_0b802c6f1a6489d52336dde1 W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab
  have iA : Integrable (fun ω =>
      (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2) P :=
    mAdd.integrable_sq
  have i₁ : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2) P :=
    m₁.integrable_sq
  have i₂ : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2) P :=
    m₂.integrable_sq
  have iS₁ : Integrable (fun ω =>
      (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2) P := iA.add i₁
  have iS : Integrable (fun ω =>
      (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2) P := iS₁.add i₂
  have hdom : Integrable (fun ω => 3 / 4 *
      ((LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2)) P := iS.const_mul _
  have hpol := LevyStochCalc.Brownian.Ito.smul_two_polarQuadVarIncrement_ae W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab.le
  have hpt : (fun ω =>
      (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2)
      ≤ᵐ[P] fun ω => 3 / 4 *
        ((LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
          + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2
          + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2) := by
    filter_upwards [hpol] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul] at hω
    have hpe : LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω
        = (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
            - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
            - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) / 2 := by linarith
    rw [hpe]
    nlinarith [sq_nonneg (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
        + LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω),
      sq_nonneg (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
        + LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω),
      sq_nonneg (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
        - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω)]
  have hsplit : ∫ ω,
      ((LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2) ∂P
      = (∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2 ∂P)
        + (∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2 ∂P)
        + ∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2 ∂P := by
    rw [MeasureTheory.integral_add iS₁ i₂, MeasureTheory.integral_add iA i₁]
  refine ⟨hmp.integrable_sq, ?_⟩
  have hstep : ∫ ω,
      (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b ω) ^ 2 ∂P
      ≤ 3 / 4 * ((∫ ω,
          (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω) ^ 2 ∂P)
        + (∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω) ^ 2 ∂P)
        + ∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) ^ 2 ∂P) := by
    have := MeasureTheory.integral_mono_ae hmp.integrable_sq hdom hpt
    rwa [MeasureTheory.integral_const_mul, hsplit] at this
  refine hstep.trans ?_
  have hC4 : (0 : ℝ) ≤ (2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4 := by
    have hcg : (0 : ℝ) ≤ LevyStochCalc.Brownian.Ito.gaussianFourthMoment := LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg
    positivity
  have hba2 : (0 : ℝ) ≤ (b - a) ^ 2 := sq_nonneg _
  nlinarith [lAdd, l₁, l₂, mul_nonneg hC4 hba2]
end Bounds

end Polarised

end LevyStochCalc.Brownian.Ito


