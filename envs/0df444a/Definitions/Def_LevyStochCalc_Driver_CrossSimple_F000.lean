-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CrossSimple_F000
-- name    : LevyStochCalc_Driver_CrossSimple_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:17:59.264438+00:00
-- url     : https://prove2.me/theorems/a4c5b9cf-05ac-4b34-941d-787e1a02482b
-- title:
--   Source declarations: LevyStochCalc.Driver.CrossSimple
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CrossSimple. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F001
import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F002
import Definitions.Def_LevyStochCalc_Driver_CrossElementary_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Elementary integrals against the two drivers are orthogonal

An elementary Brownian integral and the compensated integral of a mark-step integrand expand
into finite sums of cross terms, one for each pair of cells. Clamping a cell to a running time
either collapses it, killing the term, or leaves its left endpoint alone, where the coefficient
is measurable; so every term has zero mean and the pairing vanishes at any pair of times.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open Brownian.Multidim.MultidimBrownianMotion (min_eq_or_lt_min)

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- A Brownian increment and a compensated mass, both with bounded coefficients, have an
integrable product. -/
theorem integrable_cross_term (D : LevyDriver.{u, v, w} P d ν) {i : Fin d} {p q r v : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {ξ η : Ω → ℝ} (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    Integrable (fun ω => (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
      * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω)) P :=
  Poisson.Compensated.integrable_mul_of_memLp_two
    (Brownian.Ito.memLp_mul_increment (D.W.W i) hp hpq 2 (by simp) hξm hξb)
    (Poisson.Compensated.memLp_bdd_mul hηm hηb
      (Poisson.Compensated.compensated_memLp D.N (measurableSet_Ioc.prod hA)
        (Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hAν)))
/-- A single clamped cross term is integrable and has zero mean. -/
theorem integrable_and_integral_cross_clamped (𝒲 : CrossWitness D ℱ) {i : Fin d} {p q r v : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hr : 0 ≤ r) (hrv : r < v) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ) (hξm : Measurable ξ)
    {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η)
    {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) (t t' : ℝ) :
    Integrable (fun ω => (ξ ω * ((D.W.W i).W (min q t) ω - (D.W.W i).W (min p t) ω))
        * (η ω * D.N.compensated (Set.Ioc (min r t') (min v t') ×ˢ A) ω)) P
      ∧ ∫ ω, (ξ ω * ((D.W.W i).W (min q t) ω - (D.W.W i).W (min p t) ω))
        * (η ω * D.N.compensated (Set.Ioc (min r t') (min v t') ×ˢ A) ω) ∂P = 0 := by
  rcases min_eq_or_lt_min hpq t with hc | ⟨hpe, hplt⟩
  · have hz : (fun ω => (ξ ω * ((D.W.W i).W (min q t) ω - (D.W.W i).W (min p t) ω))
        * (η ω * D.N.compensated (Set.Ioc (min r t') (min v t') ×ˢ A) ω))
        = fun _ => (0 : ℝ) := by
      funext ω; rw [hc]; ring
    rw [hz]
    exact ⟨integrable_zero Ω ℝ P, integral_zero Ω ℝ⟩
  · rcases min_eq_or_lt_min hrv t' with hc' | ⟨hre, hrlt⟩
    · have hz : (fun ω => (ξ ω * ((D.W.W i).W (min q t) ω - (D.W.W i).W (min p t) ω))
          * (η ω * D.N.compensated (Set.Ioc (min r t') (min v t') ×ˢ A) ω))
          = fun _ => (0 : ℝ) := by
        funext ω
        rw [hc', Poisson.Compensated.MarkStep.compensated_Ioc_self D.N (min v t') A ω]
        ring
      rw [hz]
      exact ⟨integrable_zero Ω ℝ P, integral_zero Ω ℝ⟩
    · rw [hpe, hre]
      exact ⟨integrable_cross_term D hp hplt hA hAν hξm hξb hηm hηb,
        integral_cross_term_eq_zero 𝒲 hp hplt hr hrlt hA hAν hξ hξm hξb hη hηm hηb⟩
end LevyDriver

end LevyStochCalc.Driver


