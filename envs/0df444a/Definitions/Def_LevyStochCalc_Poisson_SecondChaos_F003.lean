-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F003
-- name    : LevyStochCalc_Poisson_SecondChaos_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T13:10:29.903181+00:00
-- url     : https://prove2.me/theorems/49907607-ef06-49cc-9115-923b4e73bdc5
-- title:
--   Source declarations: LevyStochCalc.Poisson.SecondChaos
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SecondChaos. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaos_F001
import Definitions.Def_LevyStochCalc_Poisson_SimpleChaos_F002

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

private lemma sum_prod_ite_diag {A : Type*} [Fintype A] [DecidableEq A] (f : A × A → ℝ) :
    ∑ r : A × A, (if r.1 = r.2 then f r else 0) = ∑ q : A, f (q, q) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq Finset.univ q (fun q' => f (q, q'))]
  simp
private lemma sum_prod_ite_swap {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α × α) × (α × α) → ℝ) :
    ∑ r : (α × α) × (α × α), (if Prod.swap r.1 = r.2 then f r else 0)
      = ∑ q : α × α, f (q, Prod.swap q) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (Prod.swap q) (fun q' => f (q, q'))]
  simp
end LevyStochCalc.Poisson


