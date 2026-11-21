-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoVersionExists_F001
-- name    : LevyStochCalc_Brownian_ItoVersionExists_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:29:46.504658+00:00
-- url     : https://prove2.me/theorems/ce15d917-5507-4dc9-8909-4900ab903d85
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoVersionExists
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoVersionExists. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F003
import Definitions.Def_SourceProof_a53c24ec6562d896f4419b97

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

include hC0 hCH in
/-- **A continuous adapted version exists over the augmented filtration**, with no side
conditions on the filtration: freezing `ℱ` before time `0` and augmenting by the null sets
gives a Brownian filtration that is constant before time `0` and whose time-`0` σ-algebra
contains every measurable null set. -/
theorem exists_isItoVersion_aug
    (Hp : Probability.ProgressivelyMeasurable (augFiltration ℱ P) H)
    (Hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → ℝ} (hX₀ : Measurable[ℱ 0] X₀)
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    (hbp : Probability.ProgressivelyMeasurable (augFiltration ℱ P) bdrift)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B) :
    ∃ X : ℝ → Ω → ℝ, IsItoVersion W (augFiltration ℱ P)
      (isBrownianFiltration_augFiltration hℱ) H hm Hp Hq X₀ bdrift X :=
  _root_.Prove2MeSourceProof.h_a53c24ec6562d896f4419b97 W (augFiltration ℱ P) (isBrownianFiltration_augFiltration hℱ) H hm Hp Hq
    hC0 hCH (fun _ ht => le_of_eq (augFiltration_of_nonpos ℱ P ht).symm)
    (fun _ hs h0 => measurableSet_augFiltration_of_null ℱ P hs h0)
    (fun _ hA => le_augFiltration ℱ P 0 _ (hX₀ hA)) bdrift hbm hbp hB0 hB
end Exists

end LevyStochCalc.Brownian.Ito


