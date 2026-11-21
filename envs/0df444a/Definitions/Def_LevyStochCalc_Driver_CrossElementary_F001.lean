-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CrossElementary_F001
-- name    : LevyStochCalc_Driver_CrossElementary_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:14:49.347336+00:00
-- url     : https://prove2.me/theorems/93784f6a-2fc0-4c6c-a8ad-e170bb564ab9
-- title:
--   Source declarations: LevyStochCalc.Driver.CrossElementary
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CrossElementary. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F000
import Definitions.Def_LevyStochCalc_Driver_CrossElementary_F000
import Definitions.Def_SourceProof_2f34208c7b9f4e759c37de78
import Definitions.Def_SourceProof_b6cfec7432a7d240e1732eef

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One cross term between the two drivers

A Brownian increment weighted at its left endpoint, against a compensated mass weighted at its
left endpoint, has zero mean: whichever of the two cells starts later, its increment is centred
given an enlargement of the filtration carrying the whole path of the other driver, and the
remaining factor is measurable there.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

section CrossTerm

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The cross term vanishes, when the Brownian cell starts last.** -/
theorem integral_cross_term_eq_zero_of_ge (𝒲 : CrossWitness D ℱ) {i : Fin d} {p q r v : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hrp : r ≤ p) {A : Set E} (hA : MeasurableSet A)
    {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ) (hξm : Measurable ξ)
    (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η) :
    ∫ ω, (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
      * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω) ∂P = 0 := by
  have hBmeas : MeasurableSet (Set.Ioc r v ×ˢ A) := measurableSet_Ioc.prod hA
  have hNm : Measurable fun ω => D.N.compensated (Set.Ioc r v ×ˢ A) ω := by
    change Measurable fun ω => (D.N.N ω (Set.Ioc r v ×ˢ A)).toReal
      - (Poisson.referenceIntensity ν (Set.Ioc r v ×ˢ A)).toReal
    exact ((D.N.measurable_eval hBmeas).ennreal_toReal).sub_const _
  have hYsm : StronglyMeasurable[𝒲.brownianLarger p]
      fun ω => ξ ω * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω) :=
    (hξ.mono (𝒲.brownian_le p)).mul
      ((hη.mono ((ℱ.mono hrp).trans (𝒲.brownian_le p))).mul
        (𝒲.stronglyMeasurable_compensated p hBmeas))
  have hYm : Measurable fun ω => ξ ω * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω) :=
    hξm.mul (hηm.mul hNm)
  have hrw : (fun ω => (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
        * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω))
      = fun ω => (ξ ω * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω))
        * ((D.W.W i).W q ω - (D.W.W i).W p ω) ^ 1 := by
    funext ω; rw [pow_one]; ring
  rw [hrw, _root_.Prove2MeSourceProof.h_2f34208c7b9f4e759c37de78 (D.W.W i) 𝒲.brownianLarger (𝒲.isBrownian i)
      hp hpq hYsm hYm 1,
    Brownian.Ito.integral_increment_pow_odd (D.W.W i) hp hpq odd_one, mul_zero]
/-- **The cross term vanishes.** -/
theorem integral_cross_term_eq_zero (𝒲 : CrossWitness D ℱ) {i : Fin d} {p q r v : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hr : 0 ≤ r) (hrv : r < v) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ) (hξm : Measurable ξ)
    {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η)
    {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
      * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω) ∂P = 0 := by
  rcases le_or_gt p r with hpr | hrp
  · exact _root_.Prove2MeSourceProof.h_b6cfec7432a7d240e1732eef 𝒲 hp hpq hr hrv hpr hA hAν hξ hξm hξb hη hηm hηb
  · exact integral_cross_term_eq_zero_of_ge 𝒲 hp hpq hrp.le hA hξ hξm hη hηm
end CrossTerm

end LevyDriver

end LevyStochCalc.Driver


