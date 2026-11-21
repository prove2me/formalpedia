-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleChaosRefine_F002
-- name    : LevyStochCalc_Poisson_SimpleChaosRefine_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:25:11.838929+00:00
-- url     : https://prove2.me/theorems/c29e85ab-9a20-4280-821e-124d49a2f6c1
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleChaosRefine
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleChaosRefine. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegreeComplex_F001
import Definitions.Def_LevyStochCalc_Poisson_SimpleProfile_F002
import Definitions.Def_LevyStochCalc_Probability_CharlierAdd_F000
import Definitions.Def_SourceProof_75f5d72d7cf5f46600559b33
import Definitions.Def_SourceProof_adfffb5c0bed4c951bccc3c4

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

/-- **The Hermitian Gram across two families of strips.** For finite pairwise disjoint families
`A`, `A'` of mark sets of finite intensity and the strips over `(a, b]`,
`E[D_s(c; A) conj D_t(c'; A')] = δ_(s t) s! ((b − a) ∑_(k, l) c_k conj c'_l ν(A k ∩ A' l)) ^ s`. -/
theorem integral_markedChaosDegreeC_strip_mul_conj_cross (N : PoissonRandomMeasure.{u, v, w} P ν)
    {p q : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l)) (s t : ℕ)
    (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    ∫ ω, markedChaosDegreeC N s (fun k => Set.Ioc a b ×ˢ A k) c ω
        * (starRingEnd ℂ) (markedChaosDegreeC N t (fun l => Set.Ioc a b ×ˢ A' l) c' ω) ∂P
      = if s = t then (s.factorial : ℂ) * ((((b - a : ℝ)) : ℂ) * ∑ k, ∑ l, c k
          * (starRingEnd ℂ) (c' l) * ((ν (A k ∩ A' l)).toReal : ℂ)) ^ s else 0 := by
  simp_rw [conj_markedChaosDegreeC]
  exact _root_.Prove2MeSourceProof.h_75f5d72d7cf5f46600559b33 N ha hab hA hAν hd hA' hAν' hd' s t c _
/-- **The Gram of two simple mark profiles on different families.** For simple mark profiles `G`,
`G'` and the strips of their mark sets over `(a, b]`,
`E[D_s(G) D_t(G')] = δ_(s t) s! ((b − a) ∫ G G' dν) ^ s`. -/
theorem integral_markedChaosDegree_simpleProfile_mul (N : PoissonRandomMeasure.{u, v, w} P ν)
    (G G' : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (s t : ℕ) :
    ∫ ω, markedChaosDegree N s (fun k => Set.Ioc a b ×ˢ G.B k) G.c ω
        * markedChaosDegree N t (fun l => Set.Ioc a b ×ˢ G'.B l) G'.c ω ∂P
      = if s = t then (s.factorial : ℝ) * ((b - a) * ∫ e, G.toFun e * G'.toFun e ∂ν) ^ s
        else 0 := by
  have h := integral_markedChaosDegreeC_strip_mul_conj_cross N ha hab G.B_measurable G.B_finite
    G.B_disjoint G'.B_measurable G'.B_finite G'.B_disjoint s t (fun k => (G.c k : ℂ))
    (fun l => (G'.c l : ℂ))
  simp_rw [markedChaosDegreeC_ofReal, Complex.conj_ofReal] at h
  refine Complex.ofReal_injective ?_
  rw [← integral_complex_ofReal]
  push_cast
  rw [h, _root_.Prove2MeSourceProof.h_adfffb5c0bed4c951bccc3c4]
  split_ifs
  · push_cast
    rfl
  · push_cast
    rfl
/-! ### Complex profiles on mark sets -/

/-- The degree-zero element of a complex profile is `1`. -/
@[simp] theorem markedChaosDegreeC_zero (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℂ) (ω : Ω) :
    markedChaosDegreeC N 0 B c ω = 1 := by
  rw [markedChaosDegreeC, Finset.piAntidiag_zero]
  simp [Nat.multinomial, poissonChaosProd]
end LevyStochCalc.Poisson


