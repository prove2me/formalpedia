-- Prove2me | Definitions.Def_SourceProof_0747e5a8579d432eeee00d7b
-- name    : SourceProof_0747e5a8579d432eeee00d7b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:02:54.902739+00:00
-- url     : https://prove2.me/theorems/47491470-a509-4928-bdc0-f13f50b359e3
-- title:
--   LevyStochCalc source module: SourceProof_0747e5a8579d432eeee00d7b
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.markedChaosDegreeC_one` comes from the `LevyStochCalc.Poisson.SimpleChaosRefine` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegreeComplex_F001
import Definitions.Def_LevyStochCalc_Poisson_SimpleProfile_F002
import Definitions.Def_LevyStochCalc_Probability_CharlierAdd_F000

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


theorem _root_.Prove2MeSourceProof.h_0747e5a8579d432eeee00d7b (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℂ) (ω : Ω) :
    markedChaosDegreeC N 1 B c ω = ∑ k, c k * (N.compensated (B k) ω : ℂ) := by
  classical
  rw [LevyStochCalc.Poisson.markedChaosDegreeC, _root_.Prove2MeSourceProof.h_1dd703ef30b98a779e073f75, Finset.sum_image ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have h2 : ∏ j, c j ^ (Pi.single k (1 : ℕ) j) = c k := by
      rw [Finset.prod_eq_single k]
      · simp
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [LevyStochCalc.Poisson.poissonChaosProd_single_one, Nat.multinomial_single, h2]
    norm_num
  · intro k _ l _ hkl
    by_contra hne
    have hc := congrFun hkl k
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hc
    exact absurd hc one_ne_zero
end LevyStochCalc.Poisson


