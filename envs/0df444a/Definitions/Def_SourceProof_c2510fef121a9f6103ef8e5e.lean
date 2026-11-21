-- Prove2me | Definitions.Def_SourceProof_c2510fef121a9f6103ef8e5e
-- name    : SourceProof_c2510fef121a9f6103ef8e5e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:09:53.456938+00:00
-- url     : https://prove2.me/theorems/27923c1a-90fe-4507-afaf-ac2d16c1d129
-- title:
--   LevyStochCalc source module: SourceProof_c2510fef121a9f6103ef8e5e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_ae` comes from the `LevyStochCalc.Brownian.ItoLocalityStrict` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Strict locality of the Itô integral

Two integrands that agree almost everywhere on a window have almost surely equal integrals
(`stochasticIntegralBrownian_congr_ae`), because the difference isometry turns the vanishing of
the energy of their difference into the vanishing of the second moment of the difference of the
integrals.

That upgrades the locality statement of `Brownian/ItoLocality.lean` from agreement at the times
`s ≤ τ ω` to agreement at the times `s < τ ω` (`stochasticIntegralBrownian_congr_of_lt`): the two
cut-off integrands then differ at the single time `s = τ ω`, a Lebesgue-null set of times. The
strict form is what a càdlàg path needs, since two integrands read along it can disagree exactly
at a jump time.

## Main statements

* `stochasticIntegralBrownian_congr_ae` — almost-everywhere equal integrands, almost surely
  equal integrals.
* `stochasticIntegralBrownian_congr_of_lt` — integrands agreeing strictly below a stopping time
  have the same integral at a time that stopping time has not reached.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)


theorem _root_.Prove2MeSourceProof.h_c2510fef121a9f6103ef8e5e {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂)) (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), H₁ ω s = H₂ ω s) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T := by
  have hiso := _root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hT
  have hzero : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
    have hinner : (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) =ᵐ[P] fun _ => 0 := by
      filter_upwards [h] with ω hω
      calc ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
          = ∫⁻ _ in Set.Icc (0 : ℝ) T, (0 : ℝ≥0∞) ∂volume := by
            refine lintegral_congr_ae ?_
            filter_upwards [hω] with s hs
            simp [hs]
        _ = 0 := lintegral_zero
    rw [lintegral_congr_ae hinner, lintegral_zero]
  rw [hzero] at hiso
  have hmeas : AEMeasurable (fun ω => (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω‖₊ : ℝ≥0∞) ^ 2) P := by
    have h1 := (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₁ hm₁ hp₁ hq₁ T).aestronglyMeasurable
    have h2 := (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H₂ hm₂ hp₂ hq₂ T).aestronglyMeasurable
    exact ((h1.aemeasurable.sub h2.aemeasurable).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hae := (lintegral_eq_zero_iff' hmeas).mp hiso
  filter_upwards [hae] with ω hω
  simp only [Pi.zero_apply] at hω
  have h1 : (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω‖₊ : ℝ≥0∞) = 0 := by
    by_contra hne
    exact absurd hω (pow_ne_zero 2 hne)
  have h2 : ‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω‖₊ = 0 := by
    exact_mod_cast h1
  have h3 : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω = 0 := by
    simpa using h2
  linarith [h3]
variable {τ : Ω → WithTop ℝ}

end LevyStochCalc.Brownian.Ito


