-- Prove2me | Definitions.Def_SourceProof_31c73cd44d056a474cdcae67
-- name    : SourceProof_31c73cd44d056a474cdcae67
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:56:41.881184+00:00
-- url     : https://prove2.me/theorems/8d5f73e6-e623-4536-bf3f-4ff7355b61c9
-- title:
--   LevyStochCalc source module: SourceProof_31c73cd44d056a474cdcae67
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.map_toReal_superposition` comes from the `LevyStochCalc.Poisson.PoissonSuperposition` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_31c73cd44d056a474cdcae67 {B : Set 𝓧} (hB : MeasurableSet B)
    (hfin : superIntensity r ρ B ≠ ⊤) :
    (superLaw r ρ).map (fun ω => (superposition ω B).toReal)
      = Po(ℝ, (superIntensity r ρ B).toNNReal) := by
  obtain ⟨F, hFmono, hFcof⟩ := LevyStochCalc.Poisson.exists_finset_exhaustion ι
  have hF := LevyStochCalc.Poisson.tendsto_finset_exhaustion hFmono hFcof
  set lamF : ℕ → ℝ≥0 := fun m => ∑ p ∈ F m, r p * (ρ p B).toNNReal with hlamF
  have hlam : Tendsto (fun m => ((lamF m : ℝ≥0) : ℝ)) atTop
      (𝓝 ((LevyStochCalc.Poisson.superIntensity r ρ B).toNNReal : ℝ)) := by
    have h1 : Tendsto (fun m => ∑ p ∈ F m, (r p : ℝ≥0∞) * ρ p B) atTop
        (𝓝 (LevyStochCalc.Poisson.superIntensity r ρ B)) := by
      rw [LevyStochCalc.Poisson.superIntensity_apply r ρ hB]
      exact LevyStochCalc.Poisson.tendsto_sum_exhaustion hF _
    have h2 := (ENNReal.tendsto_toReal hfin).comp h1
    refine (Filter.tendsto_congr fun m => ?_).1 h2
    simp only [Function.comp, hlamF]
    rw [ENNReal.toReal_sum fun p _ => ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  have hpt : ∀ᵐ ω ∂(LevyStochCalc.Poisson.superLaw r ρ),
      Tendsto (fun m => LevyStochCalc.Poisson.partialCount (F m) B ω) atTop (𝓝 (LevyStochCalc.Poisson.superposition ω B).toReal) := by
    filter_upwards [LevyStochCalc.Poisson.ae_lt_top_superposition r ρ hB hfin] with ω hω
    have h1 : Tendsto (fun m => ∑ p ∈ F m, (LevyStochCalc.Poisson.pieceCountOn B (ω p) : ℝ≥0∞)) atTop
        (𝓝 (LevyStochCalc.Poisson.superposition ω B)) := by
      rw [LevyStochCalc.Poisson.superposition_apply ω hB]
      exact LevyStochCalc.Poisson.tendsto_sum_exhaustion hF _
    have h2 := (ENNReal.tendsto_toReal hω.ne).comp h1
    exact (Filter.tendsto_congr fun m => LevyStochCalc.Poisson.partialCount_eq_toReal (F m) B ω).2 h2
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hmeas : Measurable fun ω : ι → LevyStochCalc.Poisson.PieceSpace 𝓧 => (LevyStochCalc.Poisson.superposition ω B).toReal :=
    (LevyStochCalc.Poisson.measurable_superposition hB).ennreal_toReal
  have hcont : Continuous fun x : ℝ => cexp (↑t * ↑x * I) := by fun_prop
  have hL : Tendsto (fun m => charFun ((LevyStochCalc.Poisson.superLaw r ρ).map (LevyStochCalc.Poisson.partialCount (F m) B)) t) atTop
      (𝓝 (charFun ((LevyStochCalc.Poisson.superLaw r ρ).map fun ω => (LevyStochCalc.Poisson.superposition ω B).toReal) t)) := by
    simp_rw [charFun_apply_real]
    rw [integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
    have hm : ∀ m, ∫ x, cexp (↑t * ↑x * I) ∂((LevyStochCalc.Poisson.superLaw r ρ).map (LevyStochCalc.Poisson.partialCount (F m) B))
        = ∫ ω, cexp (↑t * ↑(LevyStochCalc.Poisson.partialCount (F m) B ω) * I) ∂(LevyStochCalc.Poisson.superLaw r ρ) := fun m =>
      integral_map (LevyStochCalc.Poisson.measurable_partialCount (F m) hB).aemeasurable hcont.aestronglyMeasurable
    simp_rw [hm]
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun m => (hcont.measurable.comp (LevyStochCalc.Poisson.measurable_partialCount (F m) hB)).aestronglyMeasurable)
      (integrable_const 1) (fun m => ae_of_all _ fun ω => ?_) ?_
    · simp [Complex.norm_exp]
    · filter_upwards [hpt] with ω hω
      exact (((Complex.continuous_ofReal.tendsto _).comp hω).const_mul _ |>.mul_const _).cexp
  have hR : Tendsto (fun m => charFun Po(ℝ, lamF m) t) atTop
      (𝓝 (charFun Po(ℝ, (LevyStochCalc.Poisson.superIntensity r ρ B).toNNReal) t)) := by
    simp_rw [charFun_map_cast_poissonMeasure]
    exact (((Complex.continuous_ofReal.tendsto _).comp hlam).mul_const _).cexp
  simp_rw [LevyStochCalc.Poisson.map_partialCount r ρ _ hB] at hL
  exact tendsto_nhds_unique hL hR
end Law

end LevyStochCalc.Poisson


