-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F002
-- name    : LevyStochCalc_Poisson_SecondChaos_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:29:13.609514+00:00
-- url     : https://prove2.me/theorems/0b0d8ccd-901b-4cda-af62-8f8ebf7a7dc1
-- title:
--   Source declarations: LevyStochCalc.Poisson.SecondChaos
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SecondChaos. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F001
import Definitions.Def_SourceProof_bdea70b231ab4953cfcc61b0
import Definitions.Def_SourceProof_f4584744ffbd875d6b59f5b2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The degree-two chaos elements of a finite disjoint family of regions

`pairIndex k l` is the multi-degree carrying one unit at `k` and one at `l`. The chaos element of
that multi-degree is the product `Ñ(B k) Ñ(B l)` of two compensated counts when `k ≠ l`, and
`Ñ(B k) ^ 2 - N(B k)` when `k = l`. For two real profiles `c, c'` constant on each region of the
family, `markedSecondChaos N B c c'` is the quadratic polynomial
`(∑_k c_k Ñ(B k)) (∑_l c'_l Ñ(B l)) - ∑_k c_k c'_k N(B k)` in the counts of the family, and it
expands as the sum of the pair elements weighted by `c_k c'_l`.

On a pairwise disjoint family of regions of finite intensity these elements are centred, and
their Gram is `E[Ψ(c, c') Ψ(e, e')] = ⟨c, e⟩ ⟨c', e'⟩ + ⟨c, e'⟩ ⟨c', e⟩` for the bilinear form
`⟨a, a'⟩ = ∑_k a_k a'_k λ_k` built from the rates `λ_k = ν̂(B k)`; on strips
`B k = (a, b] ×ˢ A k` those rates are `(b - a) ν(A k)`. Both statements come from the
multi-degree orthogonality of `Poisson/SimpleChaos.lean`, the norming `∏_k α_k ! λ_k ^ α_k` at a
pair index, and the fact that two pair indices agree exactly when the pairs agree up to order.

Pairwise disjointness of the family is a hypothesis throughout; overlapping regions are not
covered. The bilinear form is degenerate wherever `λ_k = 0`, and the Gram reads `0 = 0` there.

## Main statements

* `LevyStochCalc.Poisson.pairIndex_eq_iff` — `pairIndex k l = pairIndex k' l'` exactly when
  `(k, l)` and `(k', l')` agree, possibly after a swap.
* `LevyStochCalc.Poisson.poissonChaosProd_pairIndex` — the pair element in closed form,
  `Ñ(B k) Ñ(B l) - δ_(k l) N(B k)`.
* `LevyStochCalc.Poisson.prod_pairIndex_norming` — the norming `∏_k α_k ! λ_k ^ α_k` at a pair
  index is `λ_k λ_l`, doubled on the diagonal.
* `LevyStochCalc.Poisson.integral_poissonChaosProd_pairIndex_mul` — the bilinear moment of two
  pair elements.
* `LevyStochCalc.Poisson.markedSecondChaos_eq_sum` — the quadratic element is the sum of the
  pair elements weighted by `c_k c'_l`.
* `LevyStochCalc.Poisson.integral_markedSecondChaos` — the quadratic elements are centred.
* `LevyStochCalc.Poisson.integral_markedSecondChaos_mul` — the Gram
  `⟨c, e⟩ ⟨c', e'⟩ + ⟨c, e'⟩ ⟨c', e⟩`.
* `LevyStochCalc.Poisson.integral_markedSecondChaos_strip_mul` — the same on strips
  `(a, b] ×ˢ A k` over pairwise disjoint mark sets of finite intensity, at the rates
  `(b - a) ν(A k)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The multi-degree of a pair of indices -/

/-- The bilinear moment of two pair chaos elements of a finite pairwise disjoint family of
regions of finite intensity. -/
theorem integral_poissonChaosProd_pairIndex_mul (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (k l k' l' : Fin p) :
    ∫ ω, poissonChaosProd N (pairIndex k l) B ω
        * poissonChaosProd N (pairIndex k' l') B ω ∂P
      = (if k = k' ∧ l = l' then (referenceIntensity ν (B k)).toReal
            * (referenceIntensity ν (B l)).toReal else 0)
        + (if k = l' ∧ l = k' then (referenceIntensity ν (B k)).toReal
            * (referenceIntensity ν (B l)).toReal else 0) := by
  classical
  rw [_root_.Prove2MeSourceProof.h_54f512cf38cabda215ff60d2 N hB hd hfin,
    _root_.Prove2MeSourceProof.h_bdea70b231ab4953cfcc61b0 (fun j => (referenceIntensity ν (B j)).toReal) k l]
  by_cases hp : pairIndex k l = pairIndex k' l'
  · rw [if_pos hp]
    rcases (_root_.Prove2MeSourceProof.h_f4584744ffbd875d6b59f5b2 k l k' l').1 hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · by_cases hkl : k = l
      · subst hkl; simp; ring
      · simp [hkl]
    · by_cases hkl : k = l
      · subst hkl; simp; ring
      · simp [hkl]
  · rw [if_neg hp]
    have c1 : ¬(k = k' ∧ l = l') := fun h =>
      hp ((_root_.Prove2MeSourceProof.h_f4584744ffbd875d6b59f5b2 k l k' l').2 (Or.inl h))
    have c2 : ¬(k = l' ∧ l = k') := fun h =>
      hp ((_root_.Prove2MeSourceProof.h_f4584744ffbd875d6b59f5b2 k l k' l').2 (Or.inr h))
    rw [if_neg c1, if_neg c2, add_zero]
/-- The chaos element of a pair of indices, in closed form. -/
lemma poissonChaosProd_pairIndex (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (k l : Fin p) (ω : Ω) :
    poissonChaosProd N (pairIndex k l) B ω
      = N.compensated (B k) ω * N.compensated (B l) ω
        - (if k = l then (N.N ω (B k)).toReal else 0) := by
  classical
  by_cases hkl : k = l
  · subst hkl
    rw [poissonChaosProd_pairIndex_self, if_pos rfl, sq]
  · rw [poissonChaosProd_pairIndex_of_ne N B hkl, if_neg hkl, sub_zero]
/-! ### The quadratic element of two profiles -/

/-- The degree-two chaos element of a finite family of regions carried by two profiles constant
on each region: the product of the two compensated integrals minus the count of their product. -/
noncomputable def markedSecondChaos (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c c' : Fin p → ℝ) (ω : Ω) : ℝ :=
  (∑ k, c k * N.compensated (B k) ω) * (∑ l, c' l * N.compensated (B l) ω)
    - ∑ k, c k * c' k * (N.N ω (B k)).toReal
end LevyStochCalc.Poisson


