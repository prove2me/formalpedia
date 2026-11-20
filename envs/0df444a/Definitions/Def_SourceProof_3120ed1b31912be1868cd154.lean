-- Prove2me | Definitions.Def_SourceProof_3120ed1b31912be1868cd154
-- name    : SourceProof_3120ed1b31912be1868cd154
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:55:41.211175+00:00
-- url     : https://prove2.me/theorems/026ca8d0-9507-4bc8-b2dd-2996c8b5d1b5
-- title:
--   LevyStochCalc source module: SourceProof_3120ed1b31912be1868cd154
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.markedSecondChaos_eq_sum` comes from the `LevyStochCalc.Poisson.SecondChaos` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F002

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

/-! ### The quadratic element of two profiles -/


theorem _root_.Prove2MeSourceProof.h_3120ed1b31912be1868cd154 (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c c' : Fin p → ℝ) (ω : Ω) :
    markedSecondChaos N B c c' ω
      = ∑ k, ∑ l, c k * c' l * poissonChaosProd N (pairIndex k l) B ω := by
  classical
  simp_rw [LevyStochCalc.Poisson.poissonChaosProd_pairIndex, mul_sub, Finset.sum_sub_distrib, LevyStochCalc.Poisson.markedSecondChaos,
    Finset.sum_mul_sum]
  refine congrArg₂ (· - ·) ?_ ?_
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · intro hk; exact absurd (Finset.mem_univ k) hk
end LevyStochCalc.Poisson


