-- Prove2me | Definitions.Def_SourceProof_252ed50ad1c55539aff7f986
-- name    : SourceProof_252ed50ad1c55539aff7f986
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:02:04.272119+00:00
-- url     : https://prove2.me/theorems/851c7500-8402-41b9-b6a8-1d8bbb1ce724
-- title:
--   LevyStochCalc source module: SourceProof_252ed50ad1c55539aff7f986
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.integral_markedChaosDegreeC_mul` comes from the `LevyStochCalc.Poisson.SimpleChaosDegreeComplex` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegreeComplex_F000
import Definitions.Def_SourceProof_fe5db6d67c3dd41f9cc61a9c

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The degree-`s` chaos element of a complex profile

For a complex profile `c` constant on each region of a finite pairwise disjoint family of finite
intensity, the degree-`s` element `D_s(c)` is the same multinomial combination of the products of
Charlier polynomials of the counts as for a real profile, with complex coefficients; at a real
profile it is the real element, and conjugating the profile conjugates the element. The elements
are square integrable, and their bilinear non-conjugated moment is
`E[D_s(c) D_t(c')] = δ_(s t) s! (∑_k c_k c'_k λ_k) ^ s` for the rates `λ_k = ν̂(B k)`, whence the
second moment of the modulus `E‖D_s(c)‖ ^ 2 = s! (∑_k ‖c_k‖ ^ 2 λ_k) ^ s` and the non-conjugated
second moment `E[D_s(c) ^ 2] = s! (∑_k c_k ^ 2 λ_k) ^ s`; on strips `(a, b] ×ˢ A k` the rates are
`(b − a) ν(A k)`. The element carries no factor `1 / s!`.

## Main definitions

* `LevyStochCalc.Poisson.markedChaosDegreeC` — the degree-`s` element of a complex profile.

## Main statements

* `LevyStochCalc.Poisson.integral_markedChaosDegreeC_mul` — the bilinear non-conjugated moment.
* `LevyStochCalc.Poisson.integral_norm_sq_markedChaosDegreeC`,
  `LevyStochCalc.Poisson.integral_markedChaosDegreeC_sq` — the two second moments.
* `LevyStochCalc.Poisson.integral_markedChaosDegreeC_strip_sq`,
  `LevyStochCalc.Poisson.integral_norm_sq_markedChaosDegreeC_strip` — the same on strips.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Complex profiles -/


theorem _root_.Prove2MeSourceProof.h_252ed50ad1c55539aff7f986 (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s t : ℕ) (c c' : Fin p → ℂ) :
    ∫ ω, markedChaosDegreeC N s B c ω * markedChaosDegreeC N t B c' ω ∂P
      = if s = t then (s.factorial : ℂ)
          * (∑ k, c k * c' k * ((referenceIntensity ν (B k)).toReal : ℂ)) ^ s else 0 := by
  classical
  rw [funext fun ω => LevyStochCalc.Poisson.markedChaosDegreeC_mul_eq_sum N s t B c c' ω]
  rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
    ((_root_.Prove2MeSourceProof.h_2a94f92250093c132077f173 N hB hd hfin α β).ofReal).const_mul _]
  have hinner : ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
      ∫ ω, ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) t,
          ((Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k))
            * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
            * ((LevyStochCalc.Poisson.poissonChaosProd N α B ω * LevyStochCalc.Poisson.poissonChaosProd N β B ω : ℝ) : ℂ) ∂P
        = ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) t,
            ((Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
              * (if α = β then ∏ k, ((α k).factorial : ℂ)
                  * ((LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal : ℂ) ^ α k else 0) := by
    intro α _
    rw [integral_finsetSum _ fun β _ =>
      ((_root_.Prove2MeSourceProof.h_2a94f92250093c132077f173 N hB hd hfin α β).ofReal).const_mul _]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [integral_const_mul, integral_complex_ofReal,
      _root_.Prove2MeSourceProof.h_54f512cf38cabda215ff60d2 N hB hd hfin α β]
    by_cases hab : α = β
    · rw [if_pos hab, if_pos hab, Complex.ofReal_prod]
      congr 1
      exact Finset.prod_congr rfl fun k _ => by push_cast; ring
    · rw [if_neg hab, if_neg hab, Complex.ofReal_zero]
  rw [Finset.sum_congr rfl hinner]
  by_cases hst : s = t
  · subst hst
    rw [if_pos rfl]
    have hdiag : ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
        (∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
            ((Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
              * (if α = β then ∏ k, ((α k).factorial : ℂ)
                  * ((LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal : ℂ) ^ α k else 0))
          = (Nat.multinomial Finset.univ α : ℂ) * (Nat.multinomial Finset.univ α : ℂ)
              * (∏ k, ((α k).factorial : ℂ))
              * ∏ k, (c k * c' k * ((LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal : ℂ)) ^ α k := by
      intro α hα
      have hstep : ∀ β, ((Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k))
            * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
            * (if α = β then ∏ k, ((α k).factorial : ℂ)
                * ((LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal : ℂ) ^ α k else 0)
          = if α = β then ((Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
              * (∏ k, ((α k).factorial : ℂ)
                  * ((LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal : ℂ) ^ α k) else 0 := by
        intro β; rw [mul_ite, mul_zero]
      simp_rw [hstep]
      rw [Finset.sum_ite_eq _ α (fun β => ((Nat.multinomial Finset.univ α : ℂ)
        * (∏ k, c k ^ α k)) * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
        * (∏ k, ((α k).factorial : ℂ) * ((LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal : ℂ) ^ α k)),
        if_pos hα]
      have e1 : ∏ k, ((α k).factorial : ℂ)
            * ((LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal : ℂ) ^ α k
          = (∏ k, ((α k).factorial : ℂ))
            * ∏ k, ((LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal : ℂ) ^ α k := Finset.prod_mul_distrib
      have e2 : ∏ k, (c k * c' k * ((LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal : ℂ)) ^ α k
          = (∏ k, c k ^ α k) * (∏ k, c' k ^ α k)
            * ∏ k, ((LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal : ℂ) ^ α k := by
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      rw [e1, e2]
      ring
    rw [Finset.sum_congr rfl hdiag, _root_.Prove2MeSourceProof.h_fe5db6d67c3dd41f9cc61a9c s
      (fun k => c k * c' k * ((LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal : ℂ))]
  · rw [if_neg hst]
    refine Finset.sum_eq_zero fun α hα => Finset.sum_eq_zero fun β hβ => ?_
    have hne : α ≠ β := by
      rintro rfl
      exact hst (((Finset.mem_piAntidiag.1 hα).1).symm.trans (Finset.mem_piAntidiag.1 hβ).1)
    rw [if_neg hne, mul_zero]
end LevyStochCalc.Poisson


