-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleChaos_F000
-- name    : LevyStochCalc_Poisson_SimpleChaos_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T13:00:49.884819+00:00
-- url     : https://prove2.me/theorems/542cf09e-a658-4233-861e-7810460336c8
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleChaos
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleChaos. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ChaosStep_F001

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

/-- The counts of a finite family of pairwise disjoint measurable regions are jointly
independent under `P`. -/
theorem iIndepFun_count_fin (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l)) :
    iIndepFun (fun (k : Fin p) (ω : Ω) => N.N ω (B k)) P := by
  have h := N.independent_disjoint (fun o : ULift.{w} (Fin p) => B o.down)
    (fun o => hB o.down) fun o o' hoo' => hd fun h' => hoo' (by rw [ULift.ext_iff]; exact h')
  exact h.precomp (g := ULift.up.{w}) fun x y hxy => by simpa [ULift.ext_iff] using hxy
private lemma enorm_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ‖∏ i ∈ s, f i‖ₑ = ∏ i ∈ s, ‖f i‖ₑ := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih => rw [Finset.prod_cons, Finset.prod_cons, enorm_mul, ih]
/-! ### The chaos element of a multi-degree -/

/-- The chaos element of multi-degree `α` of a finite family of regions: the product over the
family of the Charlier elements of the matching degrees. -/
noncomputable def poissonChaosProd (N : PoissonRandomMeasure P ν) {p : ℕ} (α : Fin p → ℕ)
    (B : Fin p → Set (ℝ × E)) (ω : Ω) : ℝ :=
  ∏ k, poissonChaosStep N (α k) (B k) ω
/-- The chaos element of multi-degree `0` is `1`. -/
@[simp] lemma poissonChaosProd_zero (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (ω : Ω) : poissonChaosProd N (fun _ => 0) B ω = 1 := by
  simp [poissonChaosProd]
/-- The chaos element of multi-degree `Pi.single m 1` is the compensated count `Ñ(B m)`. -/
lemma poissonChaosProd_single_one (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (m : Fin p) (ω : Ω) :
    poissonChaosProd N (Pi.single m 1) B ω = N.compensated (B m) ω := by
  rw [poissonChaosProd, Finset.prod_eq_single m]
  · rw [Pi.single_eq_same, poissonChaosStep_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, poissonChaosStep_zero]
  · intro hm
    exact absurd (Finset.mem_univ m) hm
/-- A chaos element of a family of measurable regions is measurable. -/
theorem measurable_poissonChaosProd (N : PoissonRandomMeasure P ν) {p : ℕ} (α : Fin p → ℕ)
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k)) :
    Measurable (poissonChaosProd N α B) :=
  Finset.univ.measurable_prod fun k _ => measurable_poissonChaosStep N (α k) (hB k)
/-! ### Integrability -/

/-! ### Orthogonality across multi-degrees -/

end LevyStochCalc.Poisson


