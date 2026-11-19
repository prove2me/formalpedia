-- Prove2me | Definitions.Def_SourceProof_1f23144afeff765ffdd0f47d
-- name    : SourceProof_1f23144afeff765ffdd0f47d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:19:29.916568+00:00
-- url     : https://prove2.me/theorems/4baee5d2-6e93-489b-956c-3010dadd189a
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.integral_prod_range_markPhase
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PoissonSplitting_F001

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

variable {B t}

omit [IsProbabilityMeasure ρ] in

theorem _root_.Prove2MeSourceProof.h_1f23144afeff765ffdd0f47d (hB : ∀ i, MeasurableSet (B i)) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) :
    ∫ ω, ∏ j ∈ Finset.range (K ω), markPhase B t (X j ω) ∂P
      = ∑' m, (P.real (K ⁻¹' {m}) : ℂ) * (∫ x, markPhase B t x ∂ρ) ^ m := by
  have hg := LevyStochCalc.Poisson.markPhase_measurable B t hB
  set F : ℕ → Ω → ℂ := fun m ω => ∏ j ∈ Finset.range m, LevyStochCalc.Poisson.markPhase B t (X j ω) with hF
  have hF_meas : ∀ m, Measurable (F m) := fun m =>
    Finset.measurable_prod _ fun j _ => hg.comp (mX j)
  have hF_norm : ∀ m ω, ‖F m ω‖ = 1 := by
    intro m ω
    simp only [hF, norm_prod, LevyStochCalc.Poisson.norm_markPhase, Finset.prod_const_one]
  set G : ℕ → Ω → ℂ := fun m ω => ({m} : Set ℕ).indicator (fun _ => (1 : ℂ)) (K ω) * F m ω
    with hG
  have hpt : ∀ ω, (∏ j ∈ Finset.range (K ω), LevyStochCalc.Poisson.markPhase B t (X j ω)) = ∑' m, G m ω := by
    intro ω
    rw [tsum_eq_single (K ω)]
    · simp [hG, hF]
    · intro m hm
      simp only [hG]
      rw [Set.indicator_of_notMem (fun h => hm (Set.mem_singleton_iff.1 h).symm), zero_mul]
  have hG_meas : ∀ m, Measurable (G m) := fun m =>
    ((measurable_const.indicator (measurableSet_singleton m)).comp mK).mul (hF_meas m)
  have hG_norm : ∀ m ω, ‖G m ω‖ₑ = (K ⁻¹' {m}).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro m ω
    simp only [hG]
    by_cases h : K ω = m
    · have h1 : ω ∈ K ⁻¹' {m} := h
      rw [Set.indicator_of_mem (Set.mem_singleton_iff.2 h), Set.indicator_of_mem h1, one_mul,
        ← ofReal_norm, hF_norm, ENNReal.ofReal_one]
    · have h1 : ω ∉ K ⁻¹' {m} := h
      rw [Set.indicator_of_notMem (fun h' => h (Set.mem_singleton_iff.1 h')),
        Set.indicator_of_notMem h1, zero_mul, enorm_zero]
  simp_rw [hpt]
  rw [integral_tsum (fun m => (hG_meas m).aestronglyMeasurable)]
  · refine tsum_congr fun m => ?_
    have hf : AEStronglyMeasurable (fun k : ℕ => ({m} : Set ℕ).indicator (fun _ => (1 : ℂ)) k)
        (P.map K) := Measurable.aestronglyMeasurable (Measurable.of_discrete)
    have hgm : AEStronglyMeasurable
        (fun v : ℕ → 𝓧 => ∏ j ∈ Finset.range m, LevyStochCalc.Poisson.markPhase B t (v j))
        (P.map (fun ω j => X j ω)) :=
      (Finset.measurable_prod _ fun j _ => hg.comp (measurable_pi_apply j)).aestronglyMeasurable
    have h1 := hKX.integral_fun_comp_mul_comp mK.aemeasurable
      (measurable_pi_lambda _ mX).aemeasurable hf hgm
    simp only [hG, hF]
    rw [h1, LevyStochCalc.Poisson.integral_prod_markPhase hB hX mX hXi m]
    congr 1
    have hind : (fun ω => ({m} : Set ℕ).indicator (fun _ => (1 : ℂ)) (K ω))
        = (K ⁻¹' {m}).indicator (fun _ => (1 : ℂ)) := by
      funext ω
      by_cases h : K ω = m
      · rw [Set.indicator_of_mem (Set.mem_singleton_iff.2 h),
          Set.indicator_of_mem (show ω ∈ K ⁻¹' {m} from h)]
      · rw [Set.indicator_of_notMem (fun h' => h (Set.mem_singleton_iff.1 h')),
          Set.indicator_of_notMem (show ω ∉ K ⁻¹' {m} from h)]
    rw [hind, integral_indicator_const _ (mK (measurableSet_singleton m)), Complex.real_smul,
      mul_one]
  · have hle : ∀ m, ∫⁻ ω, ‖G m ω‖ₑ ∂P = P (K ⁻¹' {m}) := by
      intro m
      rw [lintegral_congr (hG_norm m),
        lintegral_indicator_const (mK (measurableSet_singleton m)), one_mul]
    simp_rw [hle]
    rw [← measure_iUnion (f := fun m => K ⁻¹' {m})
      (fun i j hij => Set.disjoint_left.2 fun ω (h1 : K ω = i) (h2 : K ω = j) =>
        hij (h1.symm.trans h2))
      (fun m => mK (measurableSet_singleton m))]
    exact measure_ne_top _ _
end CharFun

section Law

variable {n : ℕ} {B : Fin n → Set 𝓧}

end Law

end LevyStochCalc.Poisson


