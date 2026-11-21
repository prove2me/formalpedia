-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_PolarisedQuadVar_F000
-- name    : LevyStochCalc_Brownian_PolarisedQuadVar_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:20:25.350213+00:00
-- url     : https://prove2.me/theorems/176d9253-fe97-4885-ae1d-5c0c616ac7df
-- title:
--   Source declarations: LevyStochCalc.Brownian.PolarisedQuadVar
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.PolarisedQuadVar. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_DriftIncrement_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F003
import Definitions.Def_SourceProof_0a844334f53895dbf4245fb6
import Definitions.Def_SourceProof_39285c9e8cb91346b858af97

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

/-- The product of the increments of the Itô integrals of `H₁` and `H₂` against the same Brownian
motion, compensated by the window integral of `H₁·H₂`. -/
noncomputable def polarQuadVarIncrement (a b : ℝ) (ω : Ω) : ℝ :=
  (stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ b ω
      - stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ a ω)
    * (stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ b ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ a ω)
    - ((∫ u in Set.Icc (0 : ℝ) b, H₁ ω u * H₂ ω u ∂volume)
      - ∫ u in Set.Icc (0 : ℝ) a, H₁ ω u * H₂ ω u ∂volume)
include hℱ in
/-- Additivity of the Itô integral in the integrand, at every nonnegative time. -/
theorem stochasticIntegralBrownian_add_ae_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
        + stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · filter_upwards [_root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ
        (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa (le_refl (0 : ℝ)),
      _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ H₁ hm₁ hp₁ hq₁ (le_refl (0 : ℝ)),
      _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ H₂ hm₂ hp₂ hq₂ (le_refl (0 : ℝ))]
      with ω e0 e1 e2
    rw [e0, e1, e2, Pi.zero_apply, add_zero]
  · exact _root_.Prove2MeSourceProof.h_0a844334f53895dbf4245fb6 W ℱ hℱ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hma hpa hqa ht'
section Bounds

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH₁ : ∀ ω s, |H₁ ω s| ≤ C) (hCH₂ : ∀ ω s, |H₂ ω s| ≤ C)

include hC0 hCH₁ hCH₂ hm₁ hm₂ in
/-- The compensator of the sum expands by the binomial identity. -/
theorem compensator_add_sq_eq {t : ℝ} (ω : Ω) :
    ∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u + H₂ ω u) ^ 2 ∂volume
      = (∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u) ^ 2 ∂volume)
        + 2 * (∫ u in Set.Icc (0 : ℝ) t, H₁ ω u * H₂ ω u ∂volume)
        + ∫ u in Set.Icc (0 : ℝ) t, (H₂ ω u) ^ 2 ∂volume := by
  have hfin : volume (Set.Icc (0 : ℝ) t) ≠ ⊤ := (measure_Icc_lt_top).ne
  have hm₁' : Measurable (H₁ ω) := Measurable.of_uncurry_left hm₁
  have hm₂' : Measurable (H₂ ω) := Measurable.of_uncurry_left hm₂
  have hsq : ∀ x : ℝ, |x| ≤ C → x ^ 2 ≤ C ^ 2 := by
    intro x hx
    nlinarith [abs_nonneg x, sq_abs x]
  have hi₁ : IntegrableOn (fun u => (H₁ ω u) ^ 2) (Set.Icc (0 : ℝ) t) volume :=
    integrableOn_of_bounded_of_measurable (hm₁'.pow_const 2)
      (fun u => by rw [abs_of_nonneg (sq_nonneg _)]; exact hsq _ (hCH₁ ω u)) hfin
  have hi₂ : IntegrableOn (fun u => (H₂ ω u) ^ 2) (Set.Icc (0 : ℝ) t) volume :=
    integrableOn_of_bounded_of_measurable (hm₂'.pow_const 2)
      (fun u => by rw [abs_of_nonneg (sq_nonneg _)]; exact hsq _ (hCH₂ ω u)) hfin
  have hi₁₂ : IntegrableOn (fun u => 2 * (H₁ ω u * H₂ ω u)) (Set.Icc (0 : ℝ) t) volume := by
    refine integrableOn_of_bounded_of_measurable (B := 2 * C ^ 2)
      ((measurable_const).mul (hm₁'.mul hm₂')) (fun u => ?_) hfin
    change |2 * (H₁ ω u * H₂ ω u)| ≤ 2 * C ^ 2
    have habs : |2 * (H₁ ω u * H₂ ω u)| = 2 * (|H₁ ω u| * |H₂ ω u|) := by
      rw [abs_mul, abs_mul, abs_two]
    rw [habs]
    nlinarith [hCH₁ ω u, hCH₂ ω u, abs_nonneg (H₁ ω u), abs_nonneg (H₂ ω u)]
  have hexp : ∀ u : ℝ, (H₁ ω u + H₂ ω u) ^ 2
      = (H₁ ω u) ^ 2 + 2 * (H₁ ω u * H₂ ω u) + (H₂ ω u) ^ 2 := fun u => by ring
  have hcongr : ∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u + H₂ ω u) ^ 2 ∂volume
      = ∫ u in Set.Icc (0 : ℝ) t,
          ((H₁ ω u) ^ 2 + 2 * (H₁ ω u * H₂ ω u) + (H₂ ω u) ^ 2) ∂volume :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun u _ => hexp u
  have hiSum : IntegrableOn (fun u => (H₁ ω u) ^ 2 + 2 * (H₁ ω u * H₂ ω u))
      (Set.Icc (0 : ℝ) t) volume := hi₁.add hi₁₂
  rw [hcongr, MeasureTheory.integral_add hiSum hi₂,
    MeasureTheory.integral_add hi₁ hi₁₂, MeasureTheory.integral_const_mul]
include hℱ hC0 hCH₁ hCH₂ in
/-- **Polarisation.** Twice the compensated product is the compensated square increment of
`H₁ + H₂` less those of `H₁` and of `H₂`. -/
theorem smul_two_polarQuadVarIncrement_ae {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (2 : ℝ) • polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b
      =ᵐ[P] fun ω =>
        quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
          - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
          - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω := by
  have hb : (0 : ℝ) ≤ b := ha.trans hab
  filter_upwards [stochasticIntegralBrownian_add_ae_of_nonneg W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂
      hq₁ hq₂ hma hpa hqa hb,
    stochasticIntegralBrownian_add_ae_of_nonneg W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
      hma hpa hqa ha] with ω eb ea
  simp only [Pi.smul_apply, smul_eq_mul, polarQuadVarIncrement, quadVarIncrement]
  rw [eb, ea, compensator_add_sq_eq H₁ H₂ hm₁ hm₂ hC0 hCH₁ hCH₂ ω,
    compensator_add_sq_eq H₁ H₂ hm₁ hm₂ hC0 hCH₁ hCH₂ ω]
  ring
end Bounds

end Polarised

end LevyStochCalc.Brownian.Ito


