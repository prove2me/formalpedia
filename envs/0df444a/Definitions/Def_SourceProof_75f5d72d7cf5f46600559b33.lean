-- Prove2me | Definitions.Def_SourceProof_75f5d72d7cf5f46600559b33
-- name    : SourceProof_75f5d72d7cf5f46600559b33
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:23:47.64808+00:00
-- url     : https://prove2.me/theorems/420bb2d4-6b31-4197-90ab-10ad50ce344a
-- title:
--   LevyStochCalc source module: SourceProof_75f5d72d7cf5f46600559b33
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.integral_markedChaosDegreeC_strip_mul_cross` comes from the `LevyStochCalc.Poisson.SimpleChaosRefine` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosRefine_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Refinement of the degree-`s` chaos element of a profile, and its Gram across families

For a finite pairwise disjoint family `B` of regions of finite intensity and a complex profile
`c` constant on each region, the degree-`s` element `D_s(c; B)` is `s!` times the coefficient of
`X ^ s` in the product `∏_k S(λ_k, N(B k); c_k)` of the Charlier generating series of the regions,
`λ_k = ν̂(B k)`. By the Charlier addition formula a product of such series at a common scalar is
the series of the summed rates and counts, and the series at the scalar zero is `1`. Since the
count and the intensity are additive over disjoint regions, `D_s(c; B)` is unchanged, almost
surely, when each region is split into finitely many disjoint regions carrying its value and
regions carrying the value zero are added. Over the concatenation of two families the element
splits binomially, `D_s = ∑_(a + b = s) (s choose a) D_a D_b`.

Any two finite pairwise disjoint families `B`, `B'` of regions of finite intensity have a common
refinement, the points of their union sorted by the region of each family that contains them.
Passing both elements to it turns the Gram on one family into the Gram across families,

  `E[D_s(c; B) D_t(c'; B')] = δ_(s t) s! (∑_(k, l) c_k c'_l ν̂(B k ∩ B' l)) ^ s`,

and, with the conjugate, `E[D_s(c; B) conj D_t(c'; B')] = δ_(s t) s! ⟨c, c'⟩ ^ s` for the pairing
`⟨c, c'⟩ = ∑_(k, l) c_k conj c'_l ν̂(B k ∩ B' l)`. On strips `(a, b] ×ˢ A k`, `(a, b] ×ˢ A' l` the
pairing is `(b − a) ∫ f conj g dν` for the functions `f = ∑_k c_k 𝟙_(A k)`, `g = ∑_l c'_l 𝟙_(A' l)`.

## Main definitions

* `LevyStochCalc.Poisson.regionIndex` — the region of a family containing a point, if any.
* `LevyStochCalc.Poisson.commonRefinement` — the common refinement of two finite families.
* `LevyStochCalc.Poisson.markProfileC` — the function `∑_k c_k 𝟙_(A k)` of a complex profile.

## Main statements

* `LevyStochCalc.Poisson.markedChaosDegreeC_eq_coeff` — `D_s(c; B) = s! [X ^ s] ∏_k S_k`.
* `LevyStochCalc.Poisson.markedChaosDegreeC_append` — the binomial split over the concatenation
  of two families.
* `LevyStochCalc.Poisson.markedChaosDegreeC_ae_eq_of_refine` — invariance under refinement.
* `LevyStochCalc.Poisson.integral_markedChaosDegreeC_mul_cross`,
  `LevyStochCalc.Poisson.integral_markedChaosDegreeC_mul_conj_cross` — the Gram across two
  families of regions.
* `LevyStochCalc.Poisson.integral_markedChaosDegreeC_strip_mul_cross`,
  `LevyStochCalc.Poisson.integral_markedChaosDegreeC_strip_mul_conj_cross` — the same on strips.
* `LevyStochCalc.Poisson.integral_markedChaosDegreeC_strip_mul_conj_markProfileC` — the same
  through the functions of the profiles, `δ_(s t) s! ((b − a) ∫ f conj g dν) ^ s`.
* `LevyStochCalc.Poisson.integral_markedChaosDegree_simpleProfile_mul` — the real Gram of two
  simple mark profiles on different families, `δ_(s t) s! ((b − a) ∫ f g dν) ^ s`.
* `LevyStochCalc.Poisson.markedChaosDegreeC_zero`, `LevyStochCalc.Poisson.markedChaosDegreeC_one`
  — the degree-zero element is `1` and the degree-one element is `∑_k c_k Ñ(B k)`.
-/

open MeasureTheory ProbabilityTheory PowerSeries Finset
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

open LevyStochCalc.Probability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The degree element as a coefficient of a product of generating series -/

/-! ### Refinement -/

/-! ### The common refinement of two families -/

section Refinement

variable {α : Type*}

variable {p q : ℕ} {B : Fin p → Set α} {B' : Fin q → Set α}

end Refinement

/-! ### The Gram across two families -/


theorem _root_.Prove2MeSourceProof.h_75f5d72d7cf5f46600559b33 (N : PoissonRandomMeasure.{u, v, w} P ν)
    {p q : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l)) (s t : ℕ)
    (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    ∫ ω, markedChaosDegreeC N s (fun k => Set.Ioc a b ×ˢ A k) c ω
        * markedChaosDegreeC N t (fun l => Set.Ioc a b ×ˢ A' l) c' ω ∂P
      = if s = t then (s.factorial : ℂ) * ((((b - a : ℝ)) : ℂ) * ∑ k, ∑ l, c k * c' l
          * ((ν (A k ∩ A' l)).toReal : ℂ)) ^ s else 0 := by
  have hdB : Pairwise fun k l => Disjoint (Set.Ioc a b ×ˢ A k) (Set.Ioc a b ×ˢ A l) :=
    fun k l hkl => Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  have hdB' : Pairwise fun k l => Disjoint (Set.Ioc a b ×ˢ A' k) (Set.Ioc a b ×ˢ A' l) :=
    fun k l hkl => Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd' hkl) hx.2 hx'.2
  rw [LevyStochCalc.Poisson.integral_markedChaosDegreeC_mul_cross N (fun k => measurableSet_Ioc.prod (hA k)) hdB
    (fun k => LevyStochCalc.Poisson.referenceIntensity_strip_ne_top ha (hAν k))
    (fun l => measurableSet_Ioc.prod (hA' l)) hdB'
    (fun l => LevyStochCalc.Poisson.referenceIntensity_strip_ne_top ha (hAν' l)) s t c c']
  split_ifs
  · congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Set.prod_inter_prod, Set.inter_self,
      LevyStochCalc.Poisson.referenceIntensity_strip_toReal ha hab]
    push_cast
    ring
  · rfl
/-! ### Complex profiles on mark sets -/

end LevyStochCalc.Poisson


