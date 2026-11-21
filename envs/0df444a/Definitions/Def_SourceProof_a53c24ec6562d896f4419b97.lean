-- Prove2me | Definitions.Def_SourceProof_a53c24ec6562d896f4419b97
-- name    : SourceProof_a53c24ec6562d896f4419b97
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:27:38.251453+00:00
-- url     : https://prove2.me/theorems/f0ff6818-7611-4cfa-9239-4e51eb0cf9b0
-- title:
--   LevyStochCalc source module: SourceProof_a53c24ec6562d896f4419b97
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.exists_isItoVersion` comes from the `LevyStochCalc.Brownian.ItoVersionExists` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_cf3c0bc6d72699b1e0b734c3

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Existence of a continuous adapted version of an Itô process

The Itô integral has an a.e.-continuous modification by Kolmogorov–Chentsov. Zeroing its paths
on a null set makes them continuous everywhere, and the resulting process stays adapted when the
filtration contains the null sets. Adding a measurable initial value and the drift's
(Lipschitz, hence continuous) window integral gives an `IsItoVersion`.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_of_ae_eq_of_null_mem` — a σ-algebra of the filtration
  containing the null sets does not distinguish a.e.-equal functions.
* `LevyStochCalc.Brownian.Ito.dyadicApprox` — the dyadic approximation from below, whose values
  lie in a countable set.
* `LevyStochCalc.Brownian.Ito.exists_continuousAdapted_modification` — the Itô integral has a
  continuous adapted modification.
* `LevyStochCalc.Brownian.Ito.exists_isItoVersion` — a continuous adapted version exists.
* `LevyStochCalc.Brownian.Ito.exists_isItoVersion_aug` — the same over the augmented
  filtration, with no side conditions.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Exists

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_a53c24ec6562d896f4419b97
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → ℝ} (hX₀ : Measurable[ℱ 0] X₀)
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    (hbp : Probability.ProgressivelyMeasurable ℱ bdrift)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B) :
    ∃ X : ℝ → Ω → ℝ, IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X := by
  obtain ⟨Y, hYcont, hYadapt, hYmod⟩ :=
    _root_.Prove2MeSourceProof.h_cf3c0bc6d72699b1e0b734c3 W ℱ hℱ H hm hp hq hC0 hCH hℱ0 hnull
  have hle0 : ∀ t : ℝ, ℱ 0 ≤ ℱ t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact ℱ.mono ht
    · exact hℱ0 t ht.le
  refine ⟨fun t ω => X₀ ω + (∫ s in Set.Icc (0 : ℝ) t, bdrift ω s ∂volume) + Y t ω, ?_, ?_, ?_⟩
  · exact fun ω => (continuous_const.add
      (LevyStochCalc.continuous_setIntegral_Icc (Measurable.of_uncurry_left hbm) hB0 (hB ω))).add (hYcont ω)
  · intro t
    refine Measurable.stronglyMeasurable (Measurable.add (Measurable.add ?_ ?_) (hYadapt t))
    · exact fun A hA => hle0 t _ (hX₀ hA)
    · exact ((hbp.stronglyMeasurable_setIntegral measurableSet_Icc
        Set.Icc_subset_Iic_self volume).mono le_rfl).measurable
  · intro t ht
    filter_upwards [hYmod t ht] with ω hω
    rw [hω]
    rfl
end Exists

end LevyStochCalc.Brownian.Ito


