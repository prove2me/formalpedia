-- Prove2me | Definitions.Def_SourceProof_639c5d56eb5b0b845b7540f2
-- name    : SourceProof_639c5d56eb5b0b845b7540f2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:00:25.527069+00:00
-- url     : https://prove2.me/theorems/58a39968-9db0-412f-90b2-fee31ea202ba
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.integral_markPhase
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PoissonSplitting_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Poisson splitting

A Poisson number `K` of independent marks `X₀, X₁, …` with common law `ρ`, independent of `K`,
scattered over pairwise disjoint measurable sets `B₁, …, Bₙ`: the counts
`Nᵢ = ∑_{j < K} 1_{Bᵢ}(Xⱼ)` are independent, and `Nᵢ` is Poisson with mean `r ρ(Bᵢ)`.

The joint characteristic function is computed by conditioning on `K`: given `K = m`, the
marks are independent, so `𝔼 exp(i ∑ᵢ tᵢ Nᵢ) = ∑ₘ P(K = m) cₘ` with
`c = ∑ᵢ ρ(Bᵢ) e^{i tᵢ} + (1 − ∑ᵢ ρ(Bᵢ))`, and the exponential series gives
`exp(r (c − 1)) = ∏ᵢ exp(r ρ(Bᵢ) (e^{i tᵢ} − 1))`, the characteristic function of the product of
the Poisson laws.
-/

open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} [IsProbabilityMeasure ρ]
  {K : Ω → ℕ} {X : ℕ → Ω → 𝓧} {r : ℝ≥0}

section CharFun

variable {n : ℕ} (B : Fin n → Set 𝓧) (t : Fin n → ℝ)


theorem _root_.Prove2MeSourceProof.h_639c5d56eb5b0b845b7540f2 (hB : ∀ i, MeasurableSet (B i)) (hdisj : Pairwise (Disjoint on B)) :
    ∫ x, markPhase B t x ∂ρ
      = ∑ i, (ρ.real (B i) : ℂ) * exp (t i * I) + (1 - ∑ i, (ρ.real (B i) : ℂ)) := by
  classical
  have hU : MeasurableSet (⋃ i, B i) := MeasurableSet.iUnion hB
  -- pointwise decomposition of the phase
  have hpt : ∀ x, LevyStochCalc.Poisson.markPhase B t x
      = ∑ i, (B i).indicator (fun _ => exp (t i * I)) x
        + (⋃ i, B i)ᶜ.indicator (fun _ => (1 : ℂ)) x := by
    intro x
    unfold LevyStochCalc.Poisson.markPhase
    by_cases hx : x ∈ ⋃ i, B i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      have hsum : (∑ k, t k * (B k).indicator 1 x : ℝ) = t i := by
        rw [Finset.sum_eq_single i]
        · simp [Set.indicator_of_mem hi]
        · intro k _ hk
          rw [Set.indicator_of_notMem (fun hxk => hk ?_), mul_zero]
          by_contra hne
          exact Set.disjoint_left.1 (hdisj hne) hxk hi
        · simp
      rw [hsum, Finset.sum_eq_single i]
      · rw [Set.indicator_of_mem hi,
          Set.indicator_of_notMem (fun h : x ∈ (⋃ i, B i)ᶜ => h hx), add_zero]
      · intro k _ hk
        refine Set.indicator_of_notMem (fun hxk => hk ?_) _
        by_contra hne
        exact Set.disjoint_left.1 (hdisj hne) hxk hi
      · simp
    · have hsum : (∑ k, t k * (B k).indicator 1 x : ℝ) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Set.indicator_of_notMem (fun hxk => hx (Set.mem_iUnion.2 ⟨k, hxk⟩)), mul_zero]
      rw [hsum]
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      rw [Finset.sum_eq_zero fun k _ =>
        Set.indicator_of_notMem (fun hxk => hx (Set.mem_iUnion.2 ⟨k, hxk⟩)) _, zero_add,
        Set.indicator_of_mem (Set.mem_compl hx)]
  simp_rw [hpt]
  have hint1 : ∀ i, Integrable ((B i).indicator (fun _ : 𝓧 => exp (t i * I))) ρ := fun i =>
    (integrable_const _).indicator (hB i)
  have hint2 : Integrable ((⋃ i, B i)ᶜ.indicator (fun _ => (1 : ℂ))) ρ :=
    (integrable_const _).indicator hU.compl
  rw [integral_add (integrable_finsetSum _ fun i _ => hint1 i) hint2, integral_finsetSum]
  · congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_indicator_const _ (hB i), Complex.real_smul]
    · rw [integral_indicator_const _ hU.compl, Complex.real_smul, mul_one, measureReal_compl hU,
        probReal_univ]
      have hU' : ρ.real (⋃ i, B i) = ∑ i, ρ.real (B i) := by
        rw [measureReal_def, measure_iUnion hdisj hB, tsum_fintype,
          ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
        rfl
      rw [hU']
      push_cast
      ring
  · exact fun i _ => hint1 i
variable {B t}

end CharFun

section Law

variable {n : ℕ} {B : Fin n → Set 𝓧}

end Law

end LevyStochCalc.Poisson


