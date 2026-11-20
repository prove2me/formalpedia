-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleChaos_F001
-- name    : LevyStochCalc_Poisson_SimpleChaos_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T13:04:29.777969+00:00
-- url     : https://prove2.me/theorems/c87e88c3-b917-4e3e-9b29-0072d46d791f
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleChaos
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleChaos. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaos_F000
import Definitions.Def_SourceProof_2a94f92250093c132077f173

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Chaos elements of a finite disjoint family of regions

For a Poisson random measure `N` and a finite family `B : Fin p → Set (ℝ × E)` of regions,
`poissonChaosProd N α B` is the product over the family of the Charlier elements
`poissonChaosStep N (α k) (B k)`, one factor per index, of the degree prescribed by the
multi-degree `α : Fin p → ℕ`. When the regions are pairwise disjoint their counts are jointly
independent, so the one-region orthogonality of `Poisson/ChaosStep.lean` multiplies out: the
elements of distinct multi-degrees are orthogonal under `P`, the element of multi-degree `α` has
second moment given by the norming `∏_k α_k ! λ_k ^ α_k` with `λ_k = ν̂(B k)`, the elements of
nonzero multi-degree are centred, and every element whose multi-degree is not `Pi.single m 1` is
orthogonal to the compensated count `Ñ(B m)` of the family.

Pairwise disjointness of the family is a hypothesis throughout, and it is what the independence
of the counts rests on; overlapping regions are not covered. Each factor is a polynomial in the
one count `N(B k)`, so the elements here are polynomials in the `p` counts of the family.

## Main statements

* `LevyStochCalc.Poisson.iIndepFun_count_fin` — the counts of a finite pairwise disjoint family
  of measurable regions are jointly independent.
* `LevyStochCalc.Poisson.poissonChaosProd_single_one` — the element of multi-degree
  `Pi.single m 1` is the compensated count `Ñ(B m)`.
* `LevyStochCalc.Poisson.integrable_poissonChaosProd_mul`,
  `LevyStochCalc.Poisson.integrable_poissonChaosProd` — an element of a pairwise disjoint family
  of regions of finite intensity, and a product of two of them, are integrable.
* `LevyStochCalc.Poisson.memLp_two_poissonChaosProd` — such an element lies in `L²`.
* `LevyStochCalc.Poisson.integral_poissonChaosProd_mul` —
  `E[C_α C_β] = δ_(α β) ∏_k α_k ! λ_k ^ α_k`.
* `LevyStochCalc.Poisson.integral_poissonChaosProd_eq_zero` — `E[C_α] = 0` for `α ≠ 0`.
* `LevyStochCalc.Poisson.integral_poissonChaosProd_mul_compensated_eq_zero` —
  `E[C_α Ñ(B m)] = 0` for `α ≠ Pi.single m 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Joint independence of the counts of a finite disjoint family -/

/-! ### The chaos element of a multi-degree -/

/-! ### Integrability -/

/-- A chaos element of a finite pairwise disjoint family of regions of finite intensity is
integrable. -/
theorem integrable_poissonChaosProd (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (α : Fin p → ℕ) :
    Integrable (poissonChaosProd N α B) P := by
  simpa using _root_.Prove2MeSourceProof.h_2a94f92250093c132077f173 N hB hd hfin α (fun _ => 0)
/-- A chaos element of a finite pairwise disjoint family of regions of finite intensity lies in
`L²`. -/
theorem memLp_two_poissonChaosProd (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (α : Fin p → ℕ) :
    MemLp (poissonChaosProd N α B) 2 P := by
  refine (memLp_two_iff_integrable_sq
    (measurable_poissonChaosProd N α hB).aestronglyMeasurable).2 ?_
  simpa only [pow_two] using _root_.Prove2MeSourceProof.h_2a94f92250093c132077f173 N hB hd hfin α α
/-! ### Orthogonality across multi-degrees -/

end LevyStochCalc.Poisson


