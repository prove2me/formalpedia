-- Prove2me | Definitions.Def_SourceProof_15e9b29820f9078d07baa577
-- name    : SourceProof_15e9b29820f9078d07baa577
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:13:08.518604+00:00
-- url     : https://prove2.me/theorems/7eeb69cc-7e21-4f26-babc-856df9e34479
-- title:
--   LevyStochCalc source module: SourceProof_15e9b29820f9078d07baa577
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Martingale.brownianMotion_integrable` comes from the `LevyStochCalc.Brownian.Martingale` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Continuity_F000
import Definitions.Def_LevyStochCalc_Brownian_Continuity_F001
import Definitions.Def_LevyStochCalc_Brownian_Continuity_F002
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Natural filtration, martingale property, quadratic variation

Brownian motion `W` generates the *natural filtration*

  `ℱ_t := σ(W_s : s ≤ t)`,

w.r.t. which `W` is a martingale, and has *quadratic variation*

  `⟨W⟩_t = t`.

The quadratic-variation identity `(dW)² = dt` is the cornerstone of the Itô
formula; without it the second-order Taylor term in the diffusion case would
not produce the `½ σ² f''` correction.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §1.5 + §3.1.

## Proof structure

1. Construct `naturalFiltration W` via `MeasureTheory.Filtration.natural`.
2. Adaptedness is automatic via `MeasureTheory.Filtration.stronglyAdapted_natural`.
3. Conditional-expectation identity: `𝔼[W_t | ℱ_s] = W_s` reduces to
   `𝔼[W_t − W_s | ℱ_s] = 0`. This requires:
   * **σ-algebra independence**: `σ(W_t − W_s) ⊥⊥ ℱ_s` under `P`. This is the
     structure field `BrownianMotion.joint_increment_independent`, read through
     the description of `naturalFiltration W` at `s` as `⨆ j ∈ Set.Iic s, σ(W_j)`;
     it is stronger than the derived pairwise statement
     `BrownianMotion.increment_independent`.
   * **Mean zero of increment**: `𝔼[W_t − W_s] = ∫ x, x ∂(gaussianReal 0 ⟨t-s⟩) = 0`
     by `ProbabilityTheory.integral_id_gaussianReal`.
   * **`condExp_indep_eq`**: independence + measurability ⇒ `𝔼[X | ℱ] = 𝔼[X]` a.s.

## Downstream modules

The conditional-expectation identities for Brownian increments live in
`LevyStochCalc.Brownian.MartingaleCondExp`, the martingale property and the quadratic variation
`⟨W⟩_t = t` in `LevyStochCalc.Brownian.MartingaleQuadVar`, and their counterparts for the
right-continuation of the natural filtration in `LevyStochCalc.Brownian.MartingaleRightCont`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Martingale

universe u

section Moments
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_15e9b29820f9078d07baa577
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (s : ℝ) :
    MeasureTheory.Integrable (W.W s) P := by
  by_cases hs_neg : s < 0
  · -- s < 0: W_s = 0 a.s.
    refine ⟨(W.measurable_eval s).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    have h_nn : ∀ᵐ ω ∂P, ‖W.W s ω‖ₑ = 0 := by
      filter_upwards [W.negative_zero s hs_neg] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_nn]
    simp
  push Not at hs_neg
  -- s ≥ 0
  have hs := hs_neg
  by_cases hs_zero : s = 0
  · subst hs_zero
    refine ⟨(W.measurable_eval 0).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    have h_nn : ∀ᵐ ω ∂P, ‖W.W 0 ω‖ₑ = 0 := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_nn]
    simp
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs_zero)
    have h_eq : (fun ω => W.W s ω) =ᵐ[P] fun ω => W.W s ω - W.W 0 ω := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; ring
    have h_map : P.map (fun ω => W.W s ω)
        = ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩ := by
      rw [MeasureTheory.Measure.map_congr h_eq]
      have := W.increment_gaussian (le_refl 0) hs_pos
      simpa using this
    have h_int_id : MeasureTheory.Integrable (id : ℝ → ℝ)
        (ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩) :=
      MeasureTheory.memLp_one_iff_integrable.mp
        (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := ⟨s, hs⟩) 1)
    have := (MeasureTheory.integrable_map_measure (g := (id : ℝ → ℝ))
      (by fun_prop : MeasureTheory.AEStronglyMeasurable id _)
      (W.measurable_eval s).aemeasurable).mp (h_map ▸ h_int_id)
    simpa using this
end Moments

end LevyStochCalc.Brownian.Martingale


