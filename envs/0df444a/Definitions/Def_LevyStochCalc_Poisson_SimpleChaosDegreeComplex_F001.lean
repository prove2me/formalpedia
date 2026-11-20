-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegreeComplex_F001
-- name    : LevyStochCalc_Poisson_SimpleChaosDegreeComplex_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:51:38.66446+00:00
-- url     : https://prove2.me/theorems/70ce57f8-2f71-49e4-8274-006818081826
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleChaosDegreeComplex
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleChaosDegreeComplex. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegreeComplex_F000
import Definitions.Def_SourceProof_0e25f759242a2bf97a35c0b8
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

/-- The non-conjugated second moment of a complex degree element of a finite pairwise disjoint
family of regions of finite intensity: `E[D_s(c) ^ 2] = s ! (∑_k c_k ^ 2 λ_k) ^ s`. -/
theorem integral_markedChaosDegreeC_sq (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s : ℕ) (c : Fin p → ℂ) :
    ∫ ω, markedChaosDegreeC N s B c ω ^ 2 ∂P
      = (s.factorial : ℂ)
        * (∑ k, c k ^ 2 * ((referenceIntensity ν (B k)).toReal : ℂ)) ^ s := by
  have h := _root_.Prove2MeSourceProof.h_252ed50ad1c55539aff7f986 N hB hd hfin s s c c
  rw [if_pos rfl] at h
  rw [show (fun ω => markedChaosDegreeC N s B c ω ^ 2)
      = fun ω => markedChaosDegreeC N s B c ω * markedChaosDegreeC N s B c ω from
    funext fun ω => sq _, h]
  refine congrArg _ (congrArg (· ^ s) (Finset.sum_congr rfl fun k _ => ?_))
  rw [sq]
/-- The non-conjugated second moment of a complex degree element carried by strips
`(a, b] ×ˢ A k` over a finite pairwise disjoint family of mark sets of finite intensity. -/
theorem integral_markedChaosDegreeC_strip_sq (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {A : Fin p → Set E}
    (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (s : ℕ)
    (c : Fin p → ℂ) :
    ∫ ω, markedChaosDegreeC N s (fun k => Set.Ioc a b ×ˢ A k) c ω ^ 2 ∂P
      = (s.factorial : ℂ)
        * (∑ k, c k ^ 2 * (((b - a) * (ν (A k)).toReal : ℝ) : ℂ)) ^ s := by
  have hdB : Pairwise fun k l =>
      Disjoint (Set.Ioc a b ×ˢ A k) (Set.Ioc a b ×ˢ A l) := fun k l hkl =>
    Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  rw [integral_markedChaosDegreeC_sq N (fun k => measurableSet_Ioc.prod (hA k)) hdB
    (fun k => referenceIntensity_strip_ne_top ha (hAν k))]
  simp_rw [referenceIntensity_strip_toReal ha hab]
/-- The second moment of the modulus of a complex degree element carried by strips
`(a, b] ×ˢ A k` over a finite pairwise disjoint family of mark sets of finite intensity. -/
theorem integral_norm_sq_markedChaosDegreeC_strip (N : PoissonRandomMeasure.{u, v, w} P ν)
    {p : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {A : Fin p → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (s : ℕ) (c : Fin p → ℂ) :
    ∫ ω, ‖markedChaosDegreeC N s (fun k => Set.Ioc a b ×ˢ A k) c ω‖ ^ 2 ∂P
      = (s.factorial : ℝ) * (∑ k, ‖c k‖ ^ 2 * ((b - a) * (ν (A k)).toReal)) ^ s := by
  have hdB : Pairwise fun k l =>
      Disjoint (Set.Ioc a b ×ˢ A k) (Set.Ioc a b ×ˢ A l) := fun k l hkl =>
    Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  rw [_root_.Prove2MeSourceProof.h_0e25f759242a2bf97a35c0b8 N (fun k => measurableSet_Ioc.prod (hA k)) hdB
    (fun k => referenceIntensity_strip_ne_top ha (hAν k))]
  simp_rw [referenceIntensity_strip_toReal ha hab]
end LevyStochCalc.Poisson


