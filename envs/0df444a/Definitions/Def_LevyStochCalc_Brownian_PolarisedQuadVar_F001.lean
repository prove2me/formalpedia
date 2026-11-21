-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_PolarisedQuadVar_F001
-- name    : LevyStochCalc_Brownian_PolarisedQuadVar_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:23:49.021527+00:00
-- url     : https://prove2.me/theorems/8a8cb0bb-3738-43ba-baa6-81615d347103
-- title:
--   Source declarations: LevyStochCalc.Brownian.PolarisedQuadVar
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.PolarisedQuadVar. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PolarisedQuadVar_F000
import Definitions.Def_SourceProof_cb15b0bd12e621847d80c2c5

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
/-- **The compensated product is conditionally centred at the left endpoint.** -/
theorem condExp_polarQuadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b | ℱ.rightCont a]
      =ᵐ[P] 0 := by
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  have hb₁ : ∀ ω s, |H₁ ω s| ≤ 2 * C := fun ω s => (hCH₁ ω s).trans (by linarith)
  have hb₂ : ∀ ω s, |H₂ ω s| ≤ 2 * C := fun ω s => (hCH₂ ω s).trans (by linarith)
  have hba : ∀ ω s, |H₁ ω s + H₂ ω s| ≤ 2 * C := fun ω s =>
    (abs_add_le _ _).trans (by linarith [hCH₁ ω s, hCH₂ ω s])
  have iAdd := (memLp_two_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab).integrable (by norm_num)
  have i₁ := (memLp_two_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab).integrable
    (by norm_num)
  have i₂ := (memLp_two_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab).integrable
    (by norm_num)
  have cAdd := _root_.Prove2MeSourceProof.h_cb15b0bd12e621847d80c2c5 W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa ha hab.le
  have c₁ := _root_.Prove2MeSourceProof.h_cb15b0bd12e621847d80c2c5 W ℱ hℱ H₁ hm₁ hp₁ hq₁ ha hab.le
  have c₂ := _root_.Prove2MeSourceProof.h_cb15b0bd12e621847d80c2c5 W ℱ hℱ H₂ hm₂ hp₂ hq₂ ha hab.le
  have e1 := MeasureTheory.condExp_sub (iAdd.sub i₁) i₂ (ℱ.rightCont a)
  have e2 := MeasureTheory.condExp_sub iAdd i₁ (ℱ.rightCont a)
  have hcond0 : P[quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b
        - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b
        - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b | ℱ.rightCont a] =ᵐ[P] 0 := by
    filter_upwards [e1, e2, cAdd, c₁, c₂] with ω h1 h2 hA hh1 hh2
    rw [h1, Pi.sub_apply, h2, Pi.sub_apply, hA, hh1, hh2, Pi.zero_apply]
    ring
  have hpol := smul_two_polarQuadVarIncrement_ae W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab.le
  have hkey := (MeasureTheory.condExp_congr_ae hpol).trans hcond0
  have hsm := MeasureTheory.condExp_smul (μ := P) (m := ℱ.rightCont a) (2 : ℝ)
    (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b)
  filter_upwards [hkey, hsm] with ω h1 h2
  rw [h2, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  rw [Pi.zero_apply]
  linarith
end Bounds

end Polarised

end LevyStochCalc.Brownian.Ito


