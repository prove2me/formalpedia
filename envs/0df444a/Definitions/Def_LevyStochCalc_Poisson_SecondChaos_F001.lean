-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F001
-- name    : LevyStochCalc_Poisson_SecondChaos_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T13:08:55.256988+00:00
-- url     : https://prove2.me/theorems/c3a48fe7-5b6d-45e1-92b1-6588f4254ef5
-- title:
--   Source declarations: LevyStochCalc.Poisson.SecondChaos
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SecondChaos. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F000

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

/-- A pair index is nonzero. -/
lemma pairIndex_ne_zero {p : ℕ} (k l : Fin p) : pairIndex k l ≠ fun _ => 0 := by
  intro h
  have hk := congrFun h k
  simp [pairIndex] at hk
/-- The chaos element of the pair `(k, l)` is the product of the two compensated counts when
`k ≠ l`. -/
lemma poissonChaosProd_pairIndex_of_ne (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) {k l : Fin p} (hkl : k ≠ l) (ω : Ω) :
    poissonChaosProd N (pairIndex k l) B ω
      = N.compensated (B k) ω * N.compensated (B l) ω := by
  classical
  rw [poissonChaosProd]
  rw [← Finset.prod_subset (Finset.subset_univ ({k, l} : Finset (Fin p))) ?_]
  · rw [Finset.prod_pair hkl]
    simp [pairIndex, hkl, Ne.symm hkl]
  · intro j _ hj
    have hjk : j ≠ k := fun h => hj (by simp [h])
    have hjl : j ≠ l := fun h => hj (by simp [h])
    simp [pairIndex, hjk, hjl]
/-- The chaos element of the pair `(k, k)` is the degree-two Charlier element of the region
`B k`. -/
lemma poissonChaosProd_pairIndex_self (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (k : Fin p) (ω : Ω) :
    poissonChaosProd N (pairIndex k k) B ω
      = N.compensated (B k) ω ^ 2 - (N.N ω (B k)).toReal := by
  classical
  rw [poissonChaosProd, Finset.prod_eq_single k]
  · rw [show pairIndex k k k = 2 by simp [pairIndex], poissonChaosStep_two]
  · intro j _ hj
    simp [pairIndex, hj]
  · intro hk
    exact absurd (Finset.mem_univ k) hk
/-! ### The quadratic element of two profiles -/

end LevyStochCalc.Poisson


