-- Prove2me | Definitions.Def_SourceProof_0e25f759242a2bf97a35c0b8
-- name    : SourceProof_0e25f759242a2bf97a35c0b8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:50:37.088231+00:00
-- url     : https://prove2.me/theorems/31328b2d-c65a-428b-ab11-46bb93edd1d5
-- title:
--   LevyStochCalc source module: SourceProof_0e25f759242a2bf97a35c0b8
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.integral_norm_sq_markedChaosDegreeC` comes from the `LevyStochCalc.Poisson.SimpleChaosDegreeComplex` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_252ed50ad1c55539aff7f986

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


theorem _root_.Prove2MeSourceProof.h_0e25f759242a2bf97a35c0b8 (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s : ℕ) (c : Fin p → ℂ) :
    ∫ ω, ‖markedChaosDegreeC N s B c ω‖ ^ 2 ∂P
      = (s.factorial : ℝ)
        * (∑ k, ‖c k‖ ^ 2 * (referenceIntensity ν (B k)).toReal) ^ s := by
  have hpt : ∀ ω : Ω, ((‖LevyStochCalc.Poisson.markedChaosDegreeC N s B c ω‖ ^ 2 : ℝ) : ℂ)
      = LevyStochCalc.Poisson.markedChaosDegreeC N s B c ω
        * LevyStochCalc.Poisson.markedChaosDegreeC N s B (fun k => (starRingEnd ℂ) (c k)) ω := by
    intro ω
    rw [← LevyStochCalc.Poisson.conj_markedChaosDegreeC, Complex.mul_conj']
    push_cast
    ring
  have hkey : ((∫ ω, ‖LevyStochCalc.Poisson.markedChaosDegreeC N s B c ω‖ ^ 2 ∂P : ℝ) : ℂ)
      = (((s.factorial : ℝ)
          * (∑ k, ‖c k‖ ^ 2 * (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal) ^ s : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [hpt]
    rw [_root_.Prove2MeSourceProof.h_252ed50ad1c55539aff7f986 N hB hd hfin s s c (fun k => (starRingEnd ℂ) (c k)),
      if_pos rfl]
    push_cast
    congr 1
    refine congrArg (· ^ s) (Finset.sum_congr rfl fun k _ => ?_)
    rw [mul_comm (c k) _, ← Complex.normSq_eq_conj_mul_self]
    push_cast [Complex.normSq_eq_norm_sq]
    ring
  exact Complex.ofReal_inj.1 hkey
end LevyStochCalc.Poisson


