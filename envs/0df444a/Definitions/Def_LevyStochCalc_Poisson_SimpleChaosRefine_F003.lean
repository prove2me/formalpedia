-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleChaosRefine_F003
-- name    : LevyStochCalc_Poisson_SimpleChaosRefine_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:26:32.818764+00:00
-- url     : https://prove2.me/theorems/adc2a85b-707b-4d28-b102-3820f3467f40
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleChaosRefine
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleChaosRefine. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosRefine_F002

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

/-! ### Complex profiles on mark sets -/

omit [SigmaFinite ν] in
/-- On one family of pairwise disjoint mark sets the double sum of a pairing of two profiles
reduces to its diagonal. -/
theorem sum_sum_mul_measure_inter_self {p : ℕ} {A : Fin p → Set E}
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (c c' : Fin p → ℂ) :
    ∑ k, ∑ l, c k * c' l * ((ν (A k ∩ A l)).toReal : ℂ)
      = ∑ k, c k * c' k * ((ν (A k)).toReal : ℂ) := by
  classical
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun l _ hlk => by
      rw [Set.disjoint_iff_inter_eq_empty.1 (hd (Ne.symm hlk)), measure_empty,
        ENNReal.toReal_zero, Complex.ofReal_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ k) h), Set.inter_self]
/-- The complex function `∑_k c_k 𝟙_(A k)` carried by a complex profile on a family of mark
sets. -/
noncomputable def markProfileC {p : ℕ} (A : Fin p → Set E) (c : Fin p → ℂ) (e : E) : ℂ :=
  ∑ k, c k * (A k).indicator (fun _ => (1 : ℂ)) e
omit [SigmaFinite ν] in
/-- The Hermitian `L²(ν)` pairing of the functions of two complex profiles, through the
intensities of the intersections of their mark sets. -/
theorem integral_markProfileC_mul_conj {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤) (hA' : ∀ l, MeasurableSet (A' l))
    (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    ∫ e, markProfileC A c e * (starRingEnd ℂ) (markProfileC A' c' e) ∂ν
      = ∑ k, ∑ l, c k * (starRingEnd ℂ) (c' l) * ((ν (A k ∩ A' l)).toReal : ℂ) := by
  classical
  have hmeas : ∀ k l, MeasurableSet (A k ∩ A' l) := fun k l => (hA k).inter (hA' l)
  have hfin : ∀ k l, ν (A k ∩ A' l) ≠ ⊤ :=
    fun k l => ne_top_of_le_ne_top (hAν k) (measure_mono Set.inter_subset_left)
  have hpt : ∀ e, markProfileC A c e * (starRingEnd ℂ) (markProfileC A' c' e)
      = ∑ k, ∑ l, (A k ∩ A' l).indicator (fun _ => c k * (starRingEnd ℂ) (c' l)) e := by
    intro e
    rw [markProfileC, markProfileC, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hk : e ∈ A k <;> by_cases hl : e ∈ A' l <;>
      simp [Set.indicator, hk, hl]
  have hint : ∀ k l, Integrable
      (fun e => (A k ∩ A' l).indicator (fun _ => c k * (starRingEnd ℂ) (c' l)) e) ν :=
    fun k l => memLp_one_iff_integrable.1
      (memLp_indicator_const 1 (hmeas k l) _ (Or.inr (hfin k l)))
  simp_rw [hpt]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_indicator_const _ (hmeas k l), measureReal_def, Complex.real_smul]
  ring
/-- **The Hermitian Gram across two families of strips, through the profiles.** For complex
profiles on finite pairwise disjoint families `A`, `A'` of mark sets of finite intensity, with
functions `f = ∑_k c_k 𝟙_(A k)` and `g = ∑_l c'_l 𝟙_(A' l)`,
`E[D_s(c; A) conj D_t(c'; A')] = δ_(s t) s! ((b − a) ∫ f conj g dν) ^ s`. -/
theorem integral_markedChaosDegreeC_strip_mul_conj_markProfileC
    (N : PoissonRandomMeasure.{u, v, w} P ν) {p q : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {A : Fin p → Set E} {A' : Fin q → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l))
    (hA' : ∀ l, MeasurableSet (A' l)) (hAν' : ∀ l, ν (A' l) ≠ ⊤)
    (hd' : Pairwise fun k l => Disjoint (A' k) (A' l)) (s t : ℕ) (c : Fin p → ℂ)
    (c' : Fin q → ℂ) :
    ∫ ω, markedChaosDegreeC N s (fun k => Set.Ioc a b ×ˢ A k) c ω
        * (starRingEnd ℂ) (markedChaosDegreeC N t (fun l => Set.Ioc a b ×ˢ A' l) c' ω) ∂P
      = if s = t then (s.factorial : ℂ) * ((((b - a : ℝ)) : ℂ)
          * ∫ e, markProfileC A c e * (starRingEnd ℂ) (markProfileC A' c' e) ∂ν) ^ s
        else 0 := by
  rw [integral_markedChaosDegreeC_strip_mul_conj_cross N ha hab hA hAν hd hA' hAν' hd',
    integral_markProfileC_mul_conj hA hAν hA']
end LevyStochCalc.Poisson


