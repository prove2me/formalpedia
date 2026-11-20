-- Prove2me | Definitions.Def_SourceProof_aa709884346500393cc5eed1
-- name    : SourceProof_aa709884346500393cc5eed1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:57:12.560232+00:00
-- url     : https://prove2.me/theorems/9b6a6060-df54-4cd6-b983-7e2a701b1ccf
-- title:
--   LevyStochCalc source module: SourceProof_aa709884346500393cc5eed1
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_eq_top_superposition` comes from the `LevyStochCalc.Poisson.PoissonSuperposition` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PoissonSuperposition_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Superposition of independent Poisson pieces

Given weights `r p ≥ 0` and probability laws `ρ p` on a measurable space `𝓧`, indexed by a
countable type, the *superposition* is the random measure `N = ∑ₚ Nₚ` where the pieces
`Nₚ = ∑_{j < Kₚ} δ_{X_{p,j}}` are independent, `Kₚ` is Poisson with mean `r p`, and the marks
`X_{p,j}` are independent with law `ρ p`. Its intensity is `Λ = ∑ₚ r p • ρ p`.

The sample space is the product `ι → ULift ℕ × (ℕ → 𝓧)` with the product law, and the
distributional facts about a single piece reduce to Poisson splitting.
-/

open MeasureTheory ProbabilityTheory Complex Filter Function Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u

section Piece

variable {𝓧 : Type u} [MeasurableSpace 𝓧]

variable {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧) [∀ p, IsProbabilityMeasure (ρ p)]

variable {r ρ}

variable (r ρ)

variable {r ρ}

variable (r ρ)

variable [Countable ι]

end Piece

section Exhaustion

end Exhaustion

section Law

variable {𝓧 : Type u} [MeasurableSpace 𝓧] {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧)
  [∀ p, IsProbabilityMeasure (ρ p)]

variable {r ρ}

variable (r ρ)

variable [Countable ι]


theorem _root_.Prove2MeSourceProof.h_aa709884346500393cc5eed1 {B : Set 𝓧} (hB : MeasurableSet B)
    (hinf : superIntensity r ρ B = ⊤) :
    ∀ᵐ ω ∂(superLaw r ρ), superposition ω B = ⊤ := by
  obtain ⟨F, hFmono, hFcof⟩ := LevyStochCalc.Poisson.exists_finset_exhaustion ι
  have hF := LevyStochCalc.Poisson.tendsto_finset_exhaustion hFmono hFcof
  set lamF : ℕ → ℝ≥0 := fun m => ∑ p ∈ F m, r p * (ρ p B).toNNReal with hlamF
  have hlamF' : ∀ m, ((lamF m : ℝ≥0) : ℝ≥0∞) = ∑ p ∈ F m, (r p : ℝ≥0∞) * ρ p B := by
    intro m
    simp only [hlamF]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ENNReal.coe_toNNReal (measure_ne_top _ _)]
  have hlam : Tendsto (fun m => ((lamF m : ℝ≥0) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun m => ∑ p ∈ F m, (r p : ℝ≥0∞) * ρ p B) atTop (𝓝 ⊤) := by
      rw [← hinf, LevyStochCalc.Poisson.superIntensity_apply r ρ hB]
      exact LevyStochCalc.Poisson.tendsto_sum_exhaustion hF _
    rw [ENNReal.tendsto_nhds_top_iff_nat] at h1
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨m₀, hm₀⟩ := (h1 ⌈b⌉₊).exists_forall_of_atTop
    refine ⟨m₀, fun m hm => (Nat.le_ceil b).trans ?_⟩
    have h2 : ((⌈b⌉₊ : ℝ≥0) : ℝ≥0∞) ≤ (lamF m : ℝ≥0∞) := by
      rw [hlamF']
      exact_mod_cast (hm₀ m hm).le
    exact_mod_cast ENNReal.coe_le_coe.1 h2
  have hk : ∀ k : ℕ, (LevyStochCalc.Poisson.superLaw r ρ) {ω | LevyStochCalc.Poisson.superposition ω B ≤ k} = 0 := by
    intro k
    have hle : ∀ m, (LevyStochCalc.Poisson.superLaw r ρ) {ω | LevyStochCalc.Poisson.superposition ω B ≤ k}
        ≤ (LevyStochCalc.Poisson.superLaw r ρ) {ω | LevyStochCalc.Poisson.partialCount (F m) B ω ≤ k} := by
      intro m
      refine measure_mono fun ω (hω : LevyStochCalc.Poisson.superposition ω B ≤ k) => ?_
      change LevyStochCalc.Poisson.partialCount (F m) B ω ≤ k
      have h1 : (∑ p ∈ F m, (LevyStochCalc.Poisson.pieceCountOn B (ω p) : ℝ≥0∞)) ≤ k := by
        refine le_trans ?_ hω
        rw [LevyStochCalc.Poisson.superposition_apply ω hB]
        exact ENNReal.sum_le_tsum (F m)
      rw [LevyStochCalc.Poisson.partialCount_eq_toReal, ← ENNReal.toReal_natCast k]
      exact ENNReal.toReal_mono (ENNReal.natCast_ne_top k) h1
    have hlim : Tendsto (fun m => (LevyStochCalc.Poisson.superLaw r ρ) {ω | LevyStochCalc.Poisson.partialCount (F m) B ω ≤ k}) atTop
        (𝓝 0) := by
      have hIic : MeasurableSet (Set.Iic (k : ℝ)) := measurableSet_Iic
      have h1 : ∀ m, (LevyStochCalc.Poisson.superLaw r ρ) {ω | LevyStochCalc.Poisson.partialCount (F m) B ω ≤ k}
          = ∑ j ∈ Finset.range (k + 1),
              ENNReal.ofReal (Real.exp (-(lamF m : ℝ)) * (lamF m : ℝ) ^ j / j.factorial) := by
        intro m
        rw [show {ω | LevyStochCalc.Poisson.partialCount (F m) B ω ≤ k} = LevyStochCalc.Poisson.partialCount (F m) B ⁻¹' Set.Iic (k : ℝ)
            from rfl,
          ← Measure.map_apply (LevyStochCalc.Poisson.measurable_partialCount (F m) hB) hIic, LevyStochCalc.Poisson.map_partialCount r ρ _ hB,
          Measure.map_apply Measurable.of_discrete hIic]
        have : (Nat.cast : ℕ → ℝ) ⁻¹' Set.Iic (k : ℝ) = ↑(Finset.range (k + 1)) := by
          ext n
          simp
        rw [this, ← sum_measure_singleton]
        simp_rw [poissonMeasure_singleton]
        rfl
      simp_rw [h1]
      rw [← Finset.sum_const_zero (s := Finset.range (k + 1))]
      refine tendsto_finsetSum _ fun j _ => ?_
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      have h3 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp hlam).div_const
        (j.factorial : ℝ)
      rw [zero_div] at h3
      convert h3 using 2 with m
      simp only [Function.comp]
      ring
    exact le_antisymm (ge_of_tendsto' hlim hle) zero_le
  have hset : {ω : ι → LevyStochCalc.Poisson.PieceSpace 𝓧 | ¬ LevyStochCalc.Poisson.superposition ω B = ⊤}
      = ⋃ k : ℕ, {ω | LevyStochCalc.Poisson.superposition ω B ≤ k} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      refine ⟨⌈(LevyStochCalc.Poisson.superposition ω B).toReal⌉₊, (ENNReal.ofReal_toReal h).symm.le.trans ?_⟩
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
    · rintro ⟨k, hk⟩
      exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top k) hk
  rw [ae_iff, hset]
  exact measure_iUnion_null hk
end Law

end LevyStochCalc.Poisson


