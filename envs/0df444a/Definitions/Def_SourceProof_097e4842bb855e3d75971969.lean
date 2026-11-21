-- Prove2me | Definitions.Def_SourceProof_097e4842bb855e3d75971969
-- name    : SourceProof_097e4842bb855e3d75971969
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:23:14.806271+00:00
-- url     : https://prove2.me/theorems/bc4a03b3-9f37-4598-a27f-51ae88d161d6
-- title:
--   LevyStochCalc source module: SourceProof_097e4842bb855e3d75971969
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stronglyMeasurable_polarQuadVarIncrement` comes from the `LevyStochCalc.Brownian.PolarisedQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
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

include hℱ in

theorem _root_.Prove2MeSourceProof.h_097e4842bb855e3d75971969 {a b : ℝ} (hab : a ≤ b) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b) := by
  have hM₁ := _root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 W ℱ hℱ H₁ hm₁ hp₁ hq₁
  have hM₂ := _root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 W ℱ hℱ H₂ hm₂ hp₂ hq₂
  have h1b := hM₁.1 b
  have h1a := (hM₁.1 a).mono (ℱ.rightCont.mono hab)
  have h2b := hM₂.1 b
  have h2a := (hM₂.1 a).mono (ℱ.rightCont.mono hab)
  have hcb : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) b, H₁ ω u * H₂ ω u ∂volume) :=
    (((hp₁.mul hp₂).stronglyMeasurable_setIntegral measurableSet_Icc
      Set.Icc_subset_Iic_self volume).mono (ℱ.le_rightCont b))
  have hca : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) a, H₁ ω u * H₂ ω u ∂volume) :=
    ((((hp₁.mul hp₂).stronglyMeasurable_setIntegral measurableSet_Icc
      Set.Icc_subset_Iic_self volume).mono (ℱ.le_rightCont a)).mono (ℱ.rightCont.mono hab))
  exact ((h1b.sub h1a).mul (h2b.sub h2a)).sub (hcb.sub hca)
end Bounds

end Polarised

end LevyStochCalc.Brownian.Ito


