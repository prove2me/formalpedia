-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F001
-- name    : LevyStochCalc_Poisson_CompensatedPullOut_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:37:21.505436+00:00
-- url     : https://prove2.me/theorems/4759cd40-4b5c-4e8a-b398-7bf97ab64372
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedPullOut
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedPullOut. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F000
import Definitions.Def_SourceProof_1da9cef3cd7392595155fa63

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside a compensated integral

A bounded weight measurable at time `a` times the compensated integral of a marked integrand
vanishing up to `a` is the compensated integral of the weighted integrand. The identity is proved
in `L²`: the squared distance between the two sides expands, through the Itô–Lévy isometry and
the quadratic-variation martingale started at `a`, into a combination of weighted compensators
that cancels.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Vanishing

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤)

include hℱ in
/-- **The weighted quadratic variation.** For a bounded weight measurable at `a` and an
integrand vanishing up to `a`, the weighted second moment of the compensated integral at
`T ≥ a` is the weighted compensator. -/
theorem integral_mul_sq_stochasticIntegral {a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (hφa : ∀ ω s e, s ≤ a → φ ω s e = 0) {U : Ω → ℝ} (hUm : StronglyMeasurable[ℱ a] U)
    {M : ℝ} (hUb : ∀ ω, |U ω| ≤ M) :
    ∫ ω, U ω * (stochasticIntegral N ℱ hℱ φ hm hp hq T ω) ^ 2 ∂P
      = ∫ ω, U ω * compensator ν φ T ω ∂P := by
  haveI : SigmaFinite (P.trim (ℱ.rightCont.le a)) := by infer_instance
  set f : ℝ → Ω → ℝ := fun t ω =>
    (stochasticIntegral N ℱ hℱ φ hm hp hq t ω) ^ 2 - compensator ν φ t ω with hf
  have hmart : Martingale f ℱ.rightCont P :=
    _root_.Prove2MeSourceProof.h_374644549dc26783382ef252 N ℱ hℱ φ hm hp hq
  have hsq : ∀ t, Integrable (fun ω => (stochasticIntegral N ℱ hℱ φ hm hp hq t ω) ^ 2) P :=
    fun t => (stochasticIntegral_memLp N ℱ hℱ φ hm hp hq t).integrable_sq
  have hcomp : ∀ t, Integrable (compensator ν φ t) P := fun t =>
    integrable_compensator φ hm hq t
  have hint : ∀ t, Integrable (f t) P := fun t => (hsq t).sub (hcomp t)
  have hUmeas : Measurable U := hUm.measurable.mono (ℱ.le a) le_rfl
  have hUnorm : ∀ᵐ ω ∂P, ‖U ω‖ ≤ M :=
    Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hUb ω
  have hprod : Integrable (fun ω => U ω * f T ω) P :=
    (hint T).bdd_mul hUmeas.aestronglyMeasurable hUnorm
  have hUm' : StronglyMeasurable[ℱ.rightCont a] U := hUm.mono (ℱ.le_rightCont a)
  have hpull : P[(fun ω => U ω * f T ω) | ℱ.rightCont a]
      =ᵐ[P] fun ω => U ω * (P[f T | ℱ.rightCont a]) ω :=
    condExp_mul_of_stronglyMeasurable_left hUm' hprod (hint T)
  have hcond : P[f T | ℱ.rightCont a] =ᵐ[P] f a := hmart.condExp_ae_eq haT
  have hfa : f a =ᵐ[P] 0 := by
    filter_upwards [_root_.Prove2MeSourceProof.h_1da9cef3cd7392595155fa63 N hℱ φ hm hp hq ha hφa] with ω hω
    simp only [hf, hω, compensator_eq_zero_of_vanishing φ hφa, Pi.zero_apply]
    norm_num
  have hUf : ∫ ω, U ω * f T ω ∂P = 0 := by
    rw [← integral_condExp (ℱ.rightCont.le a)]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hpull, hcond, hfa] with ω e1 e2 e3
    rw [e1]
    simp only [e2, e3, Pi.zero_apply, mul_zero]
  have hexp : ∀ ω, U ω * f T ω
      = U ω * (stochasticIntegral N ℱ hℱ φ hm hp hq T ω) ^ 2 - U ω * compensator ν φ T ω :=
    fun ω => by simp only [hf]; ring
  simp_rw [hexp] at hUf
  rw [integral_sub ((hsq T).bdd_mul hUmeas.aestronglyMeasurable hUnorm)
    ((hcomp T).bdd_mul hUmeas.aestronglyMeasurable hUnorm), sub_eq_zero] at hUf
  exact hUf
end Vanishing

section Weighted

namespace MarkedHorizonIntegrand

variable {T : ℝ}

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end MarkedHorizonIntegrand

end Weighted

end LevyStochCalc.Poisson.Compensated


