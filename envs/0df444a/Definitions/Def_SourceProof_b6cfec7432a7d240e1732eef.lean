-- Prove2me | Definitions.Def_SourceProof_b6cfec7432a7d240e1732eef
-- name    : SourceProof_b6cfec7432a7d240e1732eef
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:38:51.214367+00:00
-- url     : https://prove2.me/theorems/87c54ccd-08e9-4838-aa4b-bdca0deab472
-- title:
--   LevyStochCalc source module: SourceProof_b6cfec7432a7d240e1732eef
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.integral_cross_term_eq_zero_of_le` comes from the `LevyStochCalc.Driver.CrossElementary` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F001
import Definitions.Def_LevyStochCalc_Driver_CrossElementary_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F000

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


theorem _root_.Prove2MeSourceProof.h_b6cfec7432a7d240e1732eef (𝒲 : CrossWitness D ℱ) {i : Fin d} {p q r v : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hr : 0 ≤ r) (hrv : r < v) (hpr : p ≤ r)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ) (hξm : Measurable ξ) {Mξ : ℝ}
    (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η) {Mη : ℝ}
    (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
      * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω) ∂P = 0 := by
  have hBmeas : MeasurableSet (Set.Ioc r v ×ˢ A) := measurableSet_Ioc.prod hA
  have hfin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc r v ×ˢ A) ≠ ⊤ :=
    LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hAν
  have hNm : Measurable fun ω => D.N.compensated (Set.Ioc r v ×ˢ A) ω := by
    change Measurable fun ω => (D.N.N ω (Set.Ioc r v ×ˢ A)).toReal
      - (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc r v ×ˢ A)).toReal
    exact ((D.N.measurable_eval hBmeas).ennreal_toReal).sub_const _
  have hN2 : MemLp (fun ω => D.N.compensated (Set.Ioc r v ×ˢ A) ω) 2 P :=
    LevyStochCalc.Poisson.Compensated.compensated_memLp D.N hBmeas hfin
  have hNint : Integrable (fun ω => D.N.compensated (Set.Ioc r v ×ˢ A) ω) P :=
    hN2.integrable one_le_two
  have hΔm : Measurable fun ω => (D.W.W i).W q ω - (D.W.W i).W p ω :=
    ((D.W.W i).measurable_eval q).sub ((D.W.W i).measurable_eval p)
  have hY2 : MemLp (fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))) 2 P :=
    LevyStochCalc.Poisson.Compensated.memLp_bdd_mul hηm hηb
      (LevyStochCalc.Brownian.Ito.memLp_mul_increment (D.W.W i) hp hpq 2 (by simp) hξm hξb)
  have hYsm : StronglyMeasurable[𝒲.poissonLarger r]
      fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω)) :=
    (hη.mono (𝒲.poisson_le r)).mul
      ((hξ.mono ((ℱ.mono hpr).trans (𝒲.poisson_le r))).mul
        (𝒲.measurable_increment i r p q).stronglyMeasurable)
  have hprod : Integrable (fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
      * D.N.compensated (Set.Ioc r v ×ˢ A) ω) P :=
    LevyStochCalc.Poisson.Compensated.integrable_mul_of_memLp_two hY2 hN2
  have hrw : (fun ω => (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
        * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω))
      = fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
        * D.N.compensated (Set.Ioc r v ×ˢ A) ω := by
    funext ω; ring
  rw [hrw, ← integral_condExp (𝒲.poissonLarger.le r)]
  have hpull : P[fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
        * D.N.compensated (Set.Ioc r v ×ˢ A) ω | 𝒲.poissonLarger r]
      =ᵐ[P] (fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω)))
        * P[fun ω => D.N.compensated (Set.Ioc r v ×ˢ A) ω | 𝒲.poissonLarger r] :=
    condExp_mul_of_aestronglyMeasurable_left (m := 𝒲.poissonLarger r)
      (f := fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω)))
      (g := fun ω => D.N.compensated (Set.Ioc r v ×ˢ A) ω) hYsm.aestronglyMeasurable hprod hNint
  have hcond := _root_.Prove2MeSourceProof.h_1b57c1116b3f8ea72ca9d7fe D.N 𝒲.poissonLarger
    𝒲.isPoisson hr hrv hA hAν
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hpull, hcond] with ω e1 e2
  rw [e1, Pi.mul_apply, e2, mul_zero]
  rfl
end CrossTerm

end LevyDriver

end LevyStochCalc.Driver


