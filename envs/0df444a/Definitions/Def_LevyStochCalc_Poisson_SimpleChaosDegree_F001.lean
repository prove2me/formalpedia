-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegree_F001
-- name    : LevyStochCalc_Poisson_SimpleChaosDegree_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:26:55.315183+00:00
-- url     : https://prove2.me/theorems/69667efd-5ed1-4241-b830-43872f848cfe
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleChaosDegree
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleChaosDegree. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegree_F000
import Definitions.Def_SourceProof_1dd703ef30b98a779e073f75

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

/-- The degree-one element is the combination `∑_k c_k Ñ(B k)` of the compensated counts. -/
lemma markedChaosDegree_one (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℝ) (ω : Ω) :
    markedChaosDegree N 1 B c ω = ∑ k, c k * N.compensated (B k) ω := by
  classical
  rw [markedChaosDegree, _root_.Prove2MeSourceProof.h_1dd703ef30b98a779e073f75, Finset.sum_image ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have h2 : ∏ j, c j ^ (Pi.single k (1 : ℕ) j) = c k := by
      rw [Finset.prod_eq_single k]
      · simp
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [poissonChaosProd_single_one, Nat.multinomial_single, h2]
    norm_num
  · intro k _ l _ hkl
    by_contra hne
    have hc := congrFun hkl k
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hc
    exact absurd hc one_ne_zero
/-! ### Measurability, integrability and the Gram -/

/-- The degree elements of a family of measurable regions are measurable. -/
theorem measurable_markedChaosDegree (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k)) (c : Fin p → ℝ) :
    Measurable (markedChaosDegree N s B c) :=
  Finset.measurable_sum _ fun α _ => (measurable_poissonChaosProd N α hB).const_mul _
/-- The product of two degree elements, expanded over the multi-degrees. -/
lemma markedChaosDegree_mul_eq_sum (N : PoissonRandomMeasure P ν) {p : ℕ} (s t : ℕ)
    (B : Fin p → Set (ℝ × E)) (c c' : Fin p → ℝ) (ω : Ω) :
    markedChaosDegree N s B c ω * markedChaosDegree N t B c' ω
      = ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
          ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) t,
            ((Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
              * (poissonChaosProd N α B ω * poissonChaosProd N β B ω) := by
  rw [markedChaosDegree, markedChaosDegree, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
/-- The product of two degree elements of a finite pairwise disjoint family of regions of finite
intensity is integrable. -/
theorem integrable_markedChaosDegree_mul (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s t : ℕ) (c c' : Fin p → ℝ) :
    Integrable (fun ω => markedChaosDegree N s B c ω * markedChaosDegree N t B c' ω) P := by
  rw [funext fun ω => markedChaosDegree_mul_eq_sum N s t B c c' ω]
  exact integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
    (_root_.Prove2MeSourceProof.h_2a94f92250093c132077f173 N hB hd hfin α β).const_mul _
/-- The degree elements of a finite pairwise disjoint family of regions of finite intensity are
integrable. -/
theorem integrable_markedChaosDegree (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s : ℕ) (c : Fin p → ℝ) :
    Integrable (markedChaosDegree N s B c) P := by
  simpa using integrable_markedChaosDegree_mul N hB hd hfin s 0 c c
/-- The degree elements of a finite pairwise disjoint family of regions of finite intensity are
square integrable. -/
theorem memLp_two_markedChaosDegree (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s : ℕ) (c : Fin p → ℝ) :
    MemLp (markedChaosDegree N s B c) 2 P := by
  refine (memLp_two_iff_integrable_sq
    (measurable_markedChaosDegree N s hB c).aestronglyMeasurable).2 ?_
  simpa only [pow_two] using integrable_markedChaosDegree_mul N hB hd hfin s s c c
/-! ### A one-region family and strips -/

/-! ### The degree-two element -/

end LevyStochCalc.Poisson


