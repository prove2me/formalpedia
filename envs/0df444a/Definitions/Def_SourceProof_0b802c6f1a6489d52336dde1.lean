-- Prove2me | Definitions.Def_SourceProof_0b802c6f1a6489d52336dde1
-- name    : SourceProof_0b802c6f1a6489d52336dde1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:22:50.006494+00:00
-- url     : https://prove2.me/theorems/e98f448e-248f-4c5d-8b92-044b14c4d92e
-- title:
--   LevyStochCalc source module: SourceProof_0b802c6f1a6489d52336dde1
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.memLp_two_polarQuadVarIncrement` comes from the `LevyStochCalc.Brownian.PolarisedQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PolarisedQuadVar_F000

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

theorem _root_.Prove2MeSourceProof.h_0b802c6f1a6489d52336dde1 {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b) 2 P := by
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  have hb₁ : ∀ ω s, |H₁ ω s| ≤ 2 * C := fun ω s => (hCH₁ ω s).trans (by linarith)
  have hb₂ : ∀ ω s, |H₂ ω s| ≤ 2 * C := fun ω s => (hCH₂ ω s).trans (by linarith)
  have hba : ∀ ω s, |H₁ ω s + H₂ ω s| ≤ 2 * C := fun ω s =>
    (abs_add_le _ _).trans (by linarith [hCH₁ ω s, hCH₂ ω s])
  have mAdd := LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab
  have m₁ := LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab
  have m₂ := LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab
  have hZ : MemLp (fun ω =>
      LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
        - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
        - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) 2 P := (mAdd.sub m₁).sub m₂
  have hpol := LevyStochCalc.Brownian.Ito.smul_two_polarQuadVarIncrement_ae W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab.le
  have hae : (fun ω => (1 / 2 : ℝ) *
      (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
        - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
        - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω))
      =ᵐ[P] LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b := by
    filter_upwards [hpol] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul] at hω
    linarith
  exact (hZ.const_mul (1 / 2 : ℝ)).ae_eq hae
end Bounds

end Polarised

end LevyStochCalc.Brownian.Ito


