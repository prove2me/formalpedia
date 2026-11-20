-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegree_F002
-- name    : LevyStochCalc_Poisson_SimpleChaosDegree_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:42:18.014004+00:00
-- url     : https://prove2.me/theorems/fce5a689-ba90-45f8-9989-ddd9048c244e
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleChaosDegree
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleChaosDegree. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegree_F000
import Definitions.Def_SourceProof_64aa8c065dd6350157022f6b

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

/-- The degree elements of positive degree of a finite pairwise disjoint family of regions of
finite intensity are centred under `P`. -/
theorem integral_markedChaosDegree_eq_zero (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) {s : ℕ} (hs : s ≠ 0)
    (c : Fin p → ℝ) :
    ∫ ω, markedChaosDegree N s B c ω ∂P = 0 := by
  have h := _root_.Prove2MeSourceProof.h_64aa8c065dd6350157022f6b N hB hd hfin s 0 c c
  simp only [markedChaosDegree_zero, mul_one, if_neg hs] at h
  exact h
/-! ### A one-region family and strips -/

/-- On a one-region family the multi-degrees of total degree `s` form a singleton. -/
lemma piAntidiag_univ_fin_one (s : ℕ) :
    Finset.piAntidiag (Finset.univ : Finset (Fin 1)) s = {fun _ => s} := by
  classical
  ext α
  simp only [Finset.mem_piAntidiag, Finset.mem_singleton, ne_eq, Finset.mem_univ, implies_true,
    and_true]
  constructor
  · intro hs
    funext j
    have hs1 : α 0 = s := by simpa using hs
    rw [Subsingleton.elim j 0, hs1]
  · rintro rfl
    simp
/-- On a one-region family the degree-`s` element is the degree-`s` Charlier element of the one
region, scaled by the `s`-th power of the value of the profile. -/
lemma markedChaosDegree_fin_one (N : PoissonRandomMeasure P ν) (s : ℕ)
    (B : Fin 1 → Set (ℝ × E)) (c : Fin 1 → ℝ) (ω : Ω) :
    markedChaosDegree N s B c ω = c 0 ^ s * poissonChaosStep N s (B 0) ω := by
  classical
  rw [markedChaosDegree, piAntidiag_univ_fin_one, Finset.sum_singleton]
  have hm : Nat.multinomial (Finset.univ : Finset (Fin 1)) (fun _ => s) = 1 := by simp
  rw [hm, poissonChaosProd]
  simp
/-- The Gram of the degree elements carried by strips `(a, b] ×ˢ A k` over a finite pairwise
disjoint family of mark sets of finite intensity, at the rates `(b - a) ν(A k)`. -/
theorem integral_markedChaosDegree_strip_mul (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {A : Fin p → Set E}
    (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (s t : ℕ)
    (c c' : Fin p → ℝ) :
    ∫ ω, markedChaosDegree N s (fun k => Set.Ioc a b ×ˢ A k) c ω
        * markedChaosDegree N t (fun k => Set.Ioc a b ×ˢ A k) c' ω ∂P
      = if s = t then (s.factorial : ℝ)
          * (∑ k, c k * c' k * ((b - a) * (ν (A k)).toReal)) ^ s else 0 := by
  have hdB : Pairwise fun k l =>
      Disjoint (Set.Ioc a b ×ˢ A k) (Set.Ioc a b ×ˢ A l) := fun k l hkl =>
    Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  rw [_root_.Prove2MeSourceProof.h_64aa8c065dd6350157022f6b N (fun k => measurableSet_Ioc.prod (hA k)) hdB
    (fun k => referenceIntensity_strip_ne_top ha (hAν k))]
  simp_rw [referenceIntensity_strip_toReal ha hab]
/-! ### The degree-two element -/

/-- A pair index is symmetric in its two arguments. -/
lemma pairIndex_comm {p : ℕ} (k l : Fin p) : pairIndex l k = pairIndex k l :=
  (_root_.Prove2MeSourceProof.h_f4584744ffbd875d6b59f5b2 l k k l).2 (Or.inr ⟨rfl, rfl⟩)
/-- The total degree of a pair index is two. -/
lemma sum_pairIndex {p : ℕ} (k l : Fin p) : ∑ j, pairIndex k l j = 2 := by
  classical
  simp [pairIndex, Finset.sum_add_distrib]
/-- A pair index has total degree two. -/
lemma pairIndex_mem_piAntidiag {p : ℕ} (k l : Fin p) :
    pairIndex k l ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) 2 :=
  Finset.mem_piAntidiag.2 ⟨sum_pairIndex k l, fun _ _ => Finset.mem_univ _⟩
/-- The product of a profile over a pair index. -/
lemma prod_pow_pairIndex {p : ℕ} (c : Fin p → ℝ) (k l : Fin p) :
    ∏ j, c j ^ (pairIndex k l j) = c k * c l := by
  classical
  by_cases hkl : k = l
  · subst hkl
    rw [Finset.prod_eq_single k]
    · rw [show pairIndex k k k = 2 by simp [pairIndex]]; ring
    · intro j _ hj; simp [pairIndex, hj]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  · rw [← Finset.prod_subset (Finset.subset_univ ({k, l} : Finset (Fin p))) ?_]
    · rw [Finset.prod_pair hkl]
      simp [pairIndex, hkl, Ne.symm hkl]
    · intro j _ hj
      have hjk : j ≠ k := fun h => hj (by simp [h])
      have hjl : j ≠ l := fun h => hj (by simp [h])
      simp [pairIndex, hjk, hjl]
/-- The multinomial coefficient of a pair index. -/
lemma multinomial_pairIndex {p : ℕ} (k l : Fin p) :
    (Nat.multinomial (Finset.univ : Finset (Fin p)) (pairIndex k l) : ℝ)
      = if k = l then 1 else 2 := by
  classical
  have hspec := congrArg (fun n : ℕ => (n : ℝ))
    (Nat.multinomial_spec (Finset.univ : Finset (Fin p)) (pairIndex k l))
  push_cast at hspec
  rw [sum_pairIndex] at hspec
  have hprod := _root_.Prove2MeSourceProof.h_bdea70b231ab4953cfcc61b0 (fun _ : Fin p => (1 : ℝ)) k l
  simp only [one_pow, mul_one] at hprod
  rw [hprod] at hspec
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hfac] at hspec
  by_cases hkl : k = l
  · rw [if_pos hkl]
    rw [if_pos hkl] at hspec
    linarith
  · rw [if_neg hkl]
    rw [if_neg hkl] at hspec
    linarith
/-- The pairs carrying a given pair index. -/
lemma filter_pairIndex_eq {p : ℕ} (k l : Fin p) :
    {q ∈ (Finset.univ : Finset (Fin p × Fin p)) | pairIndex q.1 q.2 = pairIndex k l}
      = ({(k, l), (l, k)} : Finset (Fin p × Fin p)) := by
  classical
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Prod.ext_iff]
  exact _root_.Prove2MeSourceProof.h_f4584744ffbd875d6b59f5b2 q.1 q.2 k l
end LevyStochCalc.Poisson


