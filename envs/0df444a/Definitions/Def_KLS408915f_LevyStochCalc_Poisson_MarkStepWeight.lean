-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepWeight
-- name    : KLS408915f_LevyStochCalc_Poisson_MarkStepWeight
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T09:23:35.246589+00:00
-- url     : https://prove2.me/theorems/8f53b362-c6a1-463c-a6cb-21cb0e17f601
-- title:
--   Addition, negation, and difference isometry for mark-step integrands
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc, commit `984dbf0b790031eac05d56fe5a84b65e15e1e932`). `MarkStep.append` concatenates the mark families of two mark-step integrands on a common grid, while `MarkStep.neg` negates all coefficients; their integrals and evaluations satisfy the corresponding additive and negative identities, and adaptedness is preserved. `lintegral_integral_sub_sq_at` applies the `ENNReal` $L^2$ isometry to the difference of two adapted mark-step integrands up to any nonnegative time. The auxiliary `integral_p_eq` rewrites the integral at a grid point as the sum over preceding complete pieces.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/MarkStepWeight.lean#L37-L238 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.MarkStepWeight`, definition bundle `KLS408915f_LevyStochCalc_Poisson_MarkStepWeight`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityDyadic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityLimit
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkApprox
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkSum
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRectSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRefinement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityShifted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityStepIntegral
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityTruncation
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleAdapted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_PoissonSuperposition
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/MarkStepWeight.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
namespace MarkStep
section Append
variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}
/-- The sum of two mark-step integrands on a common grid, by concatenating their marks. -/
def append (G G' : MarkStep Ω E ν g) : MarkStep Ω E ν g where
  K := G.K + G'.K
  B := Fin.append G.B G'.B
  B_measurable := fun k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.B_measurable k) (fun k => by
    simp only [Fin.append_right]; exact G'.B_measurable k) k
  B_finite := fun k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.B_finite k) (fun k => by
    simp only [Fin.append_right]; exact G'.B_finite k) k
  ξ := fun i => Fin.append (G.ξ i) (G'.ξ i)
  ξ_bounded := fun i k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.ξ_bounded i k) (fun k => by
    simp only [Fin.append_right]; exact G'.ξ_bounded i k) k
  ξ_measurable := fun i k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.ξ_measurable i k) (fun k => by
    simp only [Fin.append_right]; exact G'.ξ_measurable i k) k
/-- The negative of a mark-step integrand. -/
def neg (G : MarkStep Ω E ν g) : MarkStep Ω E ν g where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k ω => -G.ξ i k ω
  ξ_bounded := fun i k => by
    obtain ⟨M, hM⟩ := G.ξ_bounded i k
    exact ⟨M, fun ω => by rw [abs_neg]; exact hM ω⟩
  ξ_measurable := fun i k => (G.ξ_measurable i k).neg
variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G G' : MarkStep Ω E ν g)
lemma integral_append (t : ℝ) (ω : Ω) :
    (G.append G').integral N t ω = G.integral N t ω + G'.integral N t ω := by
  unfold integral
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ∑ k : Fin (G.K + G'.K), Fin.append (G.ξ i) (G'.ξ i) k ω
      * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t)
        ×ˢ Fin.append G.B G'.B k) ω = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
lemma eval_append (s : ℝ) (e : E) (ω : Ω) :
    (G.append G').eval s e ω = G.eval s e ω + G'.eval s e ω := by
  unfold eval
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_add]
  congr 1
  change ∑ k : Fin (G.K + G'.K), Fin.append (G.ξ i) (G'.ξ i) k ω
      * (Fin.append G.B G'.B k).indicator (fun _ => (1 : ℝ)) e = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
lemma Adapted.append {G G' : MarkStep Ω E ν g}
    (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) : (G.append G').Adapted ℱ := by
  intro i hi k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · change @StronglyMeasurable Ω ℝ _ (ℱ (g.p i))
      (Fin.append (G.ξ i) (G'.ξ i) (Fin.castAdd _ k))
    rw [Fin.append_left]
    exact hG i hi k
  · change @StronglyMeasurable Ω ℝ _ (ℱ (g.p i))
      (Fin.append (G.ξ i) (G'.ξ i) (Fin.natAdd _ k))
    rw [Fin.append_right]
    exact hG' i hi k
lemma integral_neg (t : ℝ) (ω : Ω) : G.neg.integral N t ω = -G.integral N t ω := by
  unfold integral
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  change -G.ξ i k ω * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω
    = -(G.ξ i k ω * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω)
  exact neg_mul _ _
lemma eval_neg (s : ℝ) (e : E) (ω : Ω) : G.neg.eval s e ω = -G.eval s e ω := by
  unfold eval
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  change -G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e
    = -(G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e)
  exact neg_mul _ _
lemma Adapted.neg {G : MarkStep Ω E ν g} (hG : G.Adapted ℱ) :
    G.neg.Adapted ℱ := fun i hi k => (hG i hi k).neg
include hℱ in
/-- The `L²` distance of the compensated integrals of two adapted mark-step integrands on
a common grid, up to time `t ≥ 0`, in `ℝ≥0∞` form. -/
theorem lintegral_integral_sub_sq_at (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ ω, (‖G.integral N t ω - G'.integral N t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  have key := (G.append G'.neg).lintegral_integral_sq_at N hℱ (hG.append hG'.neg) ht
  simp only [integral_append, integral_neg, eval_append, eval_neg, ← sub_eq_add_neg] at key
  exact key
end Append
section Weight
variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}
variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w)
/-- The integral of a mark-step integrand up to a grid point, as a sum over the pieces
before it. -/
lemma integral_p_eq (b : ℕ) (hb : b ≤ g.N₀) (ω : Ω) :
    G.integral N (g.p b) ω = ∑ i ∈ Finset.range b, ∑ k, G.ξ i k ω
      * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω := by
  unfold integral
  refine (Finset.sum_subset (Finset.range_subset.2 fun i hi =>
    Finset.mem_range.2 (lt_of_lt_of_le hi hb)) ?_).symm.trans
    (Finset.sum_congr rfl fun i hi => ?_)
  · intro i hi hni
    rw [Finset.mem_range] at hi hni
    have hti : g.p b ≤ g.p i := g.p_mono (not_lt.1 hni) hi.le
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [min_eq_right hti, min_eq_right (hti.trans (g.p_mono (Nat.le_succ i) hi)),
      compensated_Ioc_self, mul_zero]
  · rw [Finset.mem_range] at hi
    rw [min_eq_left (g.p_mono hi.le hb), min_eq_left (g.p_mono hi hb)]
end Weight
end MarkStep
end Compensated
end Poisson
end LevyStochCalc


