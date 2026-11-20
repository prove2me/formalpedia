-- Prove2me | Definitions.Def_SourceProof_0bafb60d3af8b952c7d84521
-- name    : SourceProof_0bafb60d3af8b952c7d84521
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:14:40.937881+00:00
-- url     : https://prove2.me/theorems/36b8f4f2-4a01-4f9f-8ad0-ede2eeba0a10
-- title:
--   LevyStochCalc source module: SourceProof_0bafb60d3af8b952c7d84521
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.integral_markedSecondChaos_mul` comes from the `LevyStochCalc.Poisson.SecondChaos` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F002
import Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F003
import Definitions.Def_SourceProof_3120ed1b31912be1868cd154

open private sum_prod_ite_diag sum_prod_ite_swap from Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F003
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


theorem _root_.Prove2MeSourceProof.h_0bafb60d3af8b952c7d84521 (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (c c' e e' : Fin p → ℝ) :
    ∫ ω, markedSecondChaos N B c c' ω * markedSecondChaos N B e e' ω ∂P
      = (∑ k, c k * e k * (referenceIntensity ν (B k)).toReal)
          * (∑ k, c' k * e' k * (referenceIntensity ν (B k)).toReal)
        + (∑ k, c k * e' k * (referenceIntensity ν (B k)).toReal)
          * (∑ k, c' k * e k * (referenceIntensity ν (B k)).toReal) := by
  classical
  have hsum : ∀ (a a' : Fin p → ℝ) (ω : Ω), LevyStochCalc.Poisson.markedSecondChaos N B a a' ω
      = ∑ q : Fin p × Fin p, a q.1 * a' q.2 * LevyStochCalc.Poisson.poissonChaosProd N (LevyStochCalc.Poisson.pairIndex q.1 q.2) B ω := by
    intro a a' ω
    rw [_root_.Prove2MeSourceProof.h_3120ed1b31912be1868cd154, Fintype.sum_prod_type]
  have hpt : (fun ω => LevyStochCalc.Poisson.markedSecondChaos N B c c' ω * LevyStochCalc.Poisson.markedSecondChaos N B e e' ω)
      = fun ω => ∑ r : (Fin p × Fin p) × (Fin p × Fin p),
          (c r.1.1 * c' r.1.2 * (e r.2.1 * e' r.2.2))
            * (LevyStochCalc.Poisson.poissonChaosProd N (LevyStochCalc.Poisson.pairIndex r.1.1 r.1.2) B ω
              * LevyStochCalc.Poisson.poissonChaosProd N (LevyStochCalc.Poisson.pairIndex r.2.1 r.2.2) B ω) := by
    funext ω
    rw [Fintype.sum_prod_type (f := fun r : (Fin p × Fin p) × (Fin p × Fin p) =>
      (c r.1.1 * c' r.1.2 * (e r.2.1 * e' r.2.2))
        * (LevyStochCalc.Poisson.poissonChaosProd N (LevyStochCalc.Poisson.pairIndex r.1.1 r.1.2) B ω
          * LevyStochCalc.Poisson.poissonChaosProd N (LevyStochCalc.Poisson.pairIndex r.2.1 r.2.2) B ω))]
    rw [hsum, hsum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => by ring
  rw [hpt, integral_finsetSum _ fun r _ =>
    Integrable.const_mul (_root_.Prove2MeSourceProof.h_2a94f92250093c132077f173 N hB hd hfin _ _) _]
  have hone : ∀ r : (Fin p × Fin p) × (Fin p × Fin p),
      ∫ ω, (c r.1.1 * c' r.1.2 * (e r.2.1 * e' r.2.2))
          * (LevyStochCalc.Poisson.poissonChaosProd N (LevyStochCalc.Poisson.pairIndex r.1.1 r.1.2) B ω
            * LevyStochCalc.Poisson.poissonChaosProd N (LevyStochCalc.Poisson.pairIndex r.2.1 r.2.2) B ω) ∂P
        = (if r.1 = r.2 then (c r.1.1 * c' r.1.2 * (e r.2.1 * e' r.2.2))
              * ((LevyStochCalc.Poisson.referenceIntensity ν (B r.1.1)).toReal
                * (LevyStochCalc.Poisson.referenceIntensity ν (B r.1.2)).toReal) else 0)
          + (if Prod.swap r.1 = r.2 then (c r.1.1 * c' r.1.2 * (e r.2.1 * e' r.2.2))
              * ((LevyStochCalc.Poisson.referenceIntensity ν (B r.1.1)).toReal
                * (LevyStochCalc.Poisson.referenceIntensity ν (B r.1.2)).toReal) else 0) := by
    intro r
    rw [integral_const_mul,
      LevyStochCalc.Poisson.integral_poissonChaosProd_pairIndex_mul N hB hd hfin r.1.1 r.1.2 r.2.1 r.2.2]
    have h1 : (r.1.1 = r.2.1 ∧ r.1.2 = r.2.2) ↔ r.1 = r.2 := by
      obtain ⟨⟨a, b⟩, ⟨a', b'⟩⟩ := r; simp [Prod.ext_iff]
    have h2 : (r.1.1 = r.2.2 ∧ r.1.2 = r.2.1) ↔ Prod.swap r.1 = r.2 := by
      obtain ⟨⟨a, b⟩, ⟨a', b'⟩⟩ := r; simp [Prod.ext_iff, and_comm]
    simp only [h1, h2, mul_add, mul_ite, mul_zero]
  simp_rw [hone]
  rw [Finset.sum_add_distrib, sum_prod_ite_diag, sum_prod_ite_swap]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      simp only [Prod.swap_prod_mk]; ring
end LevyStochCalc.Poisson


