-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F001
-- name    : LevyStochCalc_Brownian_ItoIncrement_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:54:03.537426+00:00
-- url     : https://prove2.me/theorems/765525cd-8d75-4375-9c71-5d5d3f258607
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.ItoIncrement
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.ItoIncrement in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000
import Definitions.Def_SourceProof_0d2a3821a25704fa81bdea82
import Definitions.Def_SourceProof_371bbffaec7b2a5d68568212
import Definitions.Def_SourceProof_39285c9e8cb91346b858af97
import Definitions.Def_SourceProof_969e6fb8eb30320c0ccbf403

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

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- The Itô integral of the constant integrand `1` at a time `t ≥ 0` is the Brownian value at
`t`. -/
theorem stochasticIntegralBrownian_one
    (hm : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (1 : ℝ)))
    (hp : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (1 : ℝ))
    (hq : ∀ T, 0 < T → ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
      (‖(1 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (1 : ℝ)) hm hp hq t =ᵐ[P] W.W t := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · filter_upwards [_root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ
      (fun _ _ => (1 : ℝ)) hm hp hq (le_refl (0 : ℝ)), W.initial_zero] with ω h1 h2
    simp [h1, h2]
  · have hmul : (fun (_ : Ω) (s : ℝ) =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * (1 : ℝ)) = indIoc Ω 0 t := by
      funext _ _
      simp [indIoc]
    have hm' : Measurable (Function.uncurry (indIoc Ω 0 t)) := measurable_uncurry_indIoc 0 t
    have hp' : Probability.ProgressivelyMeasurable ℱ (indIoc Ω 0 t) :=
      progressivelyMeasurable_indIoc₀ ℱ ht'
    have hq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖indIoc Ω 0 t ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      fun T hT => _root_.Prove2MeSourceProof.h_0d2a3821a25704fa81bdea82 P 0 t T hT
    have him : Measurable (Function.uncurry fun (_ : Ω) (s : ℝ) =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * (1 : ℝ)) := by
      rw [hmul]; exact hm'
    have hip : Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (s : ℝ) =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * (1 : ℝ)) := by
      rw [hmul]; exact hp'
    have hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * (1 : ℝ)‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := by
      intro T hT
      simpa [indIoc] using hq' T hT
    have hkey := _root_.Prove2MeSourceProof.h_371bbffaec7b2a5d68568212 W ℱ hℱ (fun _ _ => (1 : ℝ)) hm hp hq
      (a := 0) (b := t) le_rfl ht' him hip hiq ht'
    rw [min_self, min_eq_left ht'.le] at hkey
    have hI : stochasticIntegralBrownian W ℱ hℱ (fun (_ : Ω) (s : ℝ) =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * (1 : ℝ)) him hip hiq t
        =ᵐ[P] fun ω => W.W t ω - W.W 0 ω := by
      rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hmul him hip hiq hm' hp' hq' t]
      have h := _root_.Prove2MeSourceProof.h_969e6fb8eb30320c0ccbf403 W ℱ hℱ (a := 0) (b := t) le_rfl ht'
        hm' hp' hq' ht'.le
      rwa [min_self, min_eq_left ht'.le] at h
    filter_upwards [hkey, hI, _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ
      (fun _ _ => (1 : ℝ)) hm hp hq (le_refl (0 : ℝ)), W.initial_zero] with ω h1 h2 h3 h4
    simp only [Pi.zero_apply] at h3
    linarith [h1, h2, h3, h4]
end Indicator

end LevyStochCalc.Brownian.Ito


