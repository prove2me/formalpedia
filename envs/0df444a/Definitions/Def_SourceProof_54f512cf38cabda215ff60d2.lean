-- Prove2me | Definitions.Def_SourceProof_54f512cf38cabda215ff60d2
-- name    : SourceProof_54f512cf38cabda215ff60d2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T13:03:59.971257+00:00
-- url     : https://prove2.me/theorems/1bc09466-3d85-47a4-a28d-5a2b999ab988
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.integral_poissonChaosProd_mul
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaos_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Chaos elements of a finite disjoint family of regions

For a Poisson random measure `N` and a finite family `B : Fin p → Set (ℝ × E)` of regions,
`poissonChaosProd N α B` is the product over the family of the Charlier elements
`poissonChaosStep N (α k) (B k)`, one factor per index, of the degree prescribed by the
multi-degree `α : Fin p → ℕ`. When the regions are pairwise disjoint their counts are jointly
independent, so the one-region orthogonality of `Poisson/ChaosStep.lean` multiplies out: the
elements of distinct multi-degrees are orthogonal under `P`, the element of multi-degree `α` has
second moment given by the norming `∏_k α_k ! λ_k ^ α_k` with `λ_k = ν̂(B k)`, the elements of
nonzero multi-degree are centred, and every element whose multi-degree is not `Pi.single m 1` is
orthogonal to the compensated count `Ñ(B m)` of the family.

Pairwise disjointness of the family is a hypothesis throughout, and it is what the independence
of the counts rests on; overlapping regions are not covered. Each factor is a polynomial in the
one count `N(B k)`, so the elements here are polynomials in the `p` counts of the family.

## Main statements

* `LevyStochCalc.Poisson.iIndepFun_count_fin` — the counts of a finite pairwise disjoint family
  of measurable regions are jointly independent.
* `LevyStochCalc.Poisson.poissonChaosProd_single_one` — the element of multi-degree
  `Pi.single m 1` is the compensated count `Ñ(B m)`.
* `LevyStochCalc.Poisson.integrable_poissonChaosProd_mul`,
  `LevyStochCalc.Poisson.integrable_poissonChaosProd` — an element of a pairwise disjoint family
  of regions of finite intensity, and a product of two of them, are integrable.
* `LevyStochCalc.Poisson.memLp_two_poissonChaosProd` — such an element lies in `L²`.
* `LevyStochCalc.Poisson.integral_poissonChaosProd_mul` —
  `E[C_α C_β] = δ_(α β) ∏_k α_k ! λ_k ^ α_k`.
* `LevyStochCalc.Poisson.integral_poissonChaosProd_eq_zero` — `E[C_α] = 0` for `α ≠ 0`.
* `LevyStochCalc.Poisson.integral_poissonChaosProd_mul_compensated_eq_zero` —
  `E[C_α Ñ(B m)] = 0` for `α ≠ Pi.single m 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Joint independence of the counts of a finite disjoint family -/

/-! ### The chaos element of a multi-degree -/

/-! ### Integrability -/

/-! ### Orthogonality across multi-degrees -/


theorem _root_.Prove2MeSourceProof.h_54f512cf38cabda215ff60d2 (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (α β : Fin p → ℕ) :
    ∫ ω, poissonChaosProd N α B ω * poissonChaosProd N β B ω ∂P
      = if α = β then ∏ k, ((α k).factorial : ℝ) * (referenceIntensity ν (B k)).toReal ^ α k
        else 0 := by
  classical
  have hX : iIndepFun (fun (k : Fin p) (ω : Ω) => N.N ω (B k)) P :=
    LevyStochCalc.Poisson.iIndepFun_count_fin N B hB hd
  have hmX : ∀ k, AEMeasurable (fun ω => N.N ω (B k)) P :=
    fun k => (N.measurable_eval (hB k)).aemeasurable
  set f : Fin p → ℝ≥0∞ → ℝ := fun k x =>
    LevyStochCalc.Probability.charlierScaled (α k) (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal x.toReal
      * LevyStochCalc.Probability.charlierScaled (β k) (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal x.toReal with hf
  have hfmeas : ∀ k, Measurable (f k) := fun k =>
    (((LevyStochCalc.Probability.continuous_charlierScaled (α k) _).measurable).comp
        ENNReal.measurable_toReal).mul
      (((LevyStochCalc.Probability.continuous_charlierScaled (β k) _).measurable).comp
        ENNReal.measurable_toReal)
  have key := hX.integral_fun_prod_comp hmX fun k => (hfmeas k).aestronglyMeasurable
  have hstep : ∫ ω, LevyStochCalc.Poisson.poissonChaosProd N α B ω * LevyStochCalc.Poisson.poissonChaosProd N β B ω ∂P
      = ∏ k, (if α k = β k then ((α k).factorial : ℝ)
          * (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal ^ α k else 0) := by
    rw [show (fun ω => LevyStochCalc.Poisson.poissonChaosProd N α B ω * LevyStochCalc.Poisson.poissonChaosProd N β B ω)
        = fun ω => ∏ k, f k (N.N ω (B k)) from
      funext fun ω => by
        rw [LevyStochCalc.Poisson.poissonChaosProd, LevyStochCalc.Poisson.poissonChaosProd, ← Finset.prod_mul_distrib]; rfl]
    rw [key]
    exact Finset.prod_congr rfl fun k _ => by
      simpa [hf, LevyStochCalc.Poisson.poissonChaosStep] using _root_.Prove2MeSourceProof.h_730b6b4ed31325bc6f4a68a4 N (hB k) (hfin k)
        (α k) (β k)
  rw [hstep]
  by_cases hab : α = β
  · subst hab
    simp
  · rw [if_neg hab]
    obtain ⟨k, hk⟩ : ∃ k, α k ≠ β k := by
      by_contra hcon
      exact hab (funext fun k => not_not.1 fun h => hcon ⟨k, h⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
end LevyStochCalc.Poisson


