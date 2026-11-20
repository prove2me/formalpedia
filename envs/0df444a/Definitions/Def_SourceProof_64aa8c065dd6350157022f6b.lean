-- Prove2me | Definitions.Def_SourceProof_64aa8c065dd6350157022f6b
-- name    : SourceProof_64aa8c065dd6350157022f6b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:41:44.210178+00:00
-- url     : https://prove2.me/theorems/317ac981-08c7-44cb-bc4f-0f129a5b0e91
-- title:
--   LevyStochCalc source module: SourceProof_64aa8c065dd6350157022f6b
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.integral_markedChaosDegree_mul` comes from the `LevyStochCalc.Poisson.SimpleChaosDegree` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegree_F001
import Definitions.Def_SourceProof_fe5db6d67c3dd41f9cc61a9c

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The degree-`s` chaos element of a profile on finitely many disjoint regions

For a Poisson random measure `N` with reference intensity `ν̂`, a finite family `B` of pairwise
disjoint regions of finite intensity `λ_k = ν̂(B k)` and a profile `c` constant on each region,
the degree-`s` element `D_s(c)` is the multinomial combination
`∑_(|α| = s) (s! / ∏_k α_k!) (∏_k c_k ^ α_k) ∏_k C_(α_k)(N(B k); λ_k)` of the products of Charlier
polynomials of the counts of the regions. It is a polynomial of degree `s` in those counts: the
degree-zero element is `1`, the degree-one element is `∑_k c_k Ñ(B k)`, and on a one-region
family the element is `c ^ s` times the degree-`s` Charlier element of the region.

The degree elements are square integrable, centred in positive degree and orthogonal across
degrees, with the Gram `E[D_s(c) D_t(c')] = δ_(s t) s! ⟨c, c'⟩ ^ s` for the bilinear form
`⟨c, c'⟩ = ∑_k c_k c'_k λ_k`; on strips `(a, b] ×ˢ A k` the rates are `(b − a) ν(A k)`. The Gram
rests on the orthogonality of the products of Charlier polynomials across multi-degrees, with the
norming `∏_k α_k! λ_k ^ α_k`, and on the multinomial identity
`∑_(|α| = s) (s! / ∏ α_k!) ^ 2 (∏ α_k!) ∏ x_k ^ α_k = s! (∑ x_k) ^ s`. The degree-two element of
one profile is the quadratic element `markedSecondChaos` carried by that profile twice.

The bilinear form is degenerate on a region of zero intensity. The profile is constant on the
regions of one given family: no mode of `L²(ν)` beyond such combinations of indicators enters, and
no common refinement of two families is formed.

## Main definitions

* `LevyStochCalc.Poisson.markedChaosDegree` — the degree-`s` element of a profile on a finite
  family of regions.

## Main statements

* `LevyStochCalc.Poisson.sum_piAntidiag_multinomial_sq` — the multinomial identity behind the
  norming.
* `LevyStochCalc.Poisson.markedChaosDegree_one`, `LevyStochCalc.Poisson.markedChaosDegree_fin_one`
  — the degree-one element and the one-region case.
* `LevyStochCalc.Poisson.integral_markedChaosDegree_mul` — the Gram
  `E[D_s(c) D_t(c')] = δ_(s t) s! ⟨c, c'⟩ ^ s`.
* `LevyStochCalc.Poisson.integral_markedChaosDegree_strip_mul` — the same on strips, at the rates
  `(b − a) ν(A k)`.
* `LevyStochCalc.Poisson.markedChaosDegree_two` — the degree-two element is the quadratic element
  of the profile.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The algebraic core -/

/-! ### The degree-`s` element of a mark profile -/

/-! ### Measurability, integrability and the Gram -/


theorem _root_.Prove2MeSourceProof.h_64aa8c065dd6350157022f6b (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s t : ℕ) (c c' : Fin p → ℝ) :
    ∫ ω, markedChaosDegree N s B c ω * markedChaosDegree N t B c' ω ∂P
      = if s = t then (s.factorial : ℝ)
          * (∑ k, c k * c' k * (referenceIntensity ν (B k)).toReal) ^ s else 0 := by
  classical
  rw [funext fun ω => LevyStochCalc.Poisson.markedChaosDegree_mul_eq_sum N s t B c c' ω]
  rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
    (_root_.Prove2MeSourceProof.h_2a94f92250093c132077f173 N hB hd hfin α β).const_mul _]
  have hinner : ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
      ∫ ω, ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) t,
          ((Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k))
            * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
            * (LevyStochCalc.Poisson.poissonChaosProd N α B ω * LevyStochCalc.Poisson.poissonChaosProd N β B ω) ∂P
        = ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) t,
            ((Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
              * (if α = β then ∏ k, ((α k).factorial : ℝ)
                  * (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal ^ α k else 0) := by
    intro α _
    rw [integral_finsetSum _ fun β _ =>
      (_root_.Prove2MeSourceProof.h_2a94f92250093c132077f173 N hB hd hfin α β).const_mul _]
    exact Finset.sum_congr rfl fun β _ => by
      rw [integral_const_mul, _root_.Prove2MeSourceProof.h_54f512cf38cabda215ff60d2 N hB hd hfin α β]
  rw [Finset.sum_congr rfl hinner]
  by_cases hst : s = t
  · subst hst
    rw [if_pos rfl]
    have hdiag : ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
        (∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
            ((Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
              * (if α = β then ∏ k, ((α k).factorial : ℝ)
                  * (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal ^ α k else 0))
          = (Nat.multinomial Finset.univ α : ℝ) * (Nat.multinomial Finset.univ α : ℝ)
              * (∏ k, ((α k).factorial : ℝ))
              * ∏ k, (c k * c' k * (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal) ^ α k := by
      intro α hα
      have hstep : ∀ β, ((Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k))
            * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
            * (if α = β then ∏ k, ((α k).factorial : ℝ)
                * (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal ^ α k else 0)
          = if α = β then ((Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
              * (∏ k, ((α k).factorial : ℝ)
                  * (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal ^ α k) else 0 := by
        intro β; rw [mul_ite, mul_zero]
      simp_rw [hstep]
      rw [Finset.sum_ite_eq _ α (fun β => ((Nat.multinomial Finset.univ α : ℝ)
        * (∏ k, c k ^ α k)) * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
        * (∏ k, ((α k).factorial : ℝ)
            * (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal ^ α k)), if_pos hα]
      have e1 : ∏ k, ((α k).factorial : ℝ) * (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal ^ α k
          = (∏ k, ((α k).factorial : ℝ))
            * ∏ k, (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal ^ α k := Finset.prod_mul_distrib
      have e2 : ∏ k, (c k * c' k * (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal) ^ α k
          = (∏ k, c k ^ α k) * (∏ k, c' k ^ α k)
            * ∏ k, (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal ^ α k := by
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      rw [e1, e2]
      ring
    rw [Finset.sum_congr rfl hdiag,
      _root_.Prove2MeSourceProof.h_fe5db6d67c3dd41f9cc61a9c s (fun k => c k * c' k * (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal)]
  · rw [if_neg hst]
    refine Finset.sum_eq_zero fun α hα => Finset.sum_eq_zero fun β hβ => ?_
    have hne : α ≠ β := by
      rintro rfl
      exact hst (((Finset.mem_piAntidiag.1 hα).1).symm.trans (Finset.mem_piAntidiag.1 hβ).1)
    rw [if_neg hne, mul_zero]
/-! ### A one-region family and strips -/

/-! ### The degree-two element -/

end LevyStochCalc.Poisson


