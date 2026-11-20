-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegreeComplex_F000
-- name    : LevyStochCalc_Poisson_SimpleChaosDegreeComplex_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:45:05.231481+00:00
-- url     : https://prove2.me/theorems/8d687da0-c477-4d16-9d39-12a40e639d8f
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleChaosDegreeComplex
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleChaosDegreeComplex. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegree_F001
import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegree_F003

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

/-- The degree-`s` chaos element of a finite family of regions carried by a complex profile
constant on each region. -/
noncomputable def markedChaosDegreeC (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℂ) (ω : Ω) : ℂ :=
  ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
    (Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k)
      * (poissonChaosProd N α B ω : ℂ)
/-- At a real profile the complex element is the real one. -/
lemma markedChaosDegreeC_ofReal (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℝ) (ω : Ω) :
    markedChaosDegreeC N s B (fun k => (c k : ℂ)) ω = (markedChaosDegree N s B c ω : ℂ) := by
  rw [markedChaosDegreeC, markedChaosDegree, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  push_cast
  ring
/-- Conjugating the profile conjugates the element. -/
lemma conj_markedChaosDegreeC (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℂ) (ω : Ω) :
    (starRingEnd ℂ) (markedChaosDegreeC N s B c ω)
      = markedChaosDegreeC N s B (fun k => (starRingEnd ℂ) (c k)) ω := by
  rw [markedChaosDegreeC, markedChaosDegreeC, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, map_mul, map_prod]
  simp [map_pow]
/-- The complex degree elements of a family of measurable regions are measurable. -/
theorem measurable_markedChaosDegreeC (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k)) (c : Fin p → ℂ) :
    Measurable (markedChaosDegreeC N s B c) :=
  Finset.measurable_sum _ fun α _ =>
    (Complex.measurable_ofReal.comp (measurable_poissonChaosProd N α hB)).const_mul _
/-- The complex degree elements of a finite pairwise disjoint family of regions of finite
intensity are square integrable. -/
theorem memLp_two_markedChaosDegreeC (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s : ℕ) (c : Fin p → ℂ) :
    MemLp (markedChaosDegreeC N s B c) 2 P := by
  unfold markedChaosDegreeC
  exact memLp_finsetSum _ fun α _ =>
    ((memLp_two_poissonChaosProd N hB hd hfin α).ofReal).const_mul _
/-- The product of two complex degree elements, expanded over the multi-degrees. -/
lemma markedChaosDegreeC_mul_eq_sum (N : PoissonRandomMeasure P ν) {p : ℕ} (s t : ℕ)
    (B : Fin p → Set (ℝ × E)) (c c' : Fin p → ℂ) (ω : Ω) :
    markedChaosDegreeC N s B c ω * markedChaosDegreeC N t B c' ω
      = ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
          ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) t,
            ((Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
              * ((poissonChaosProd N α B ω * poissonChaosProd N β B ω : ℝ) : ℂ) := by
  rw [markedChaosDegreeC, markedChaosDegreeC, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  push_cast
  ring
end LevyStochCalc.Poisson


