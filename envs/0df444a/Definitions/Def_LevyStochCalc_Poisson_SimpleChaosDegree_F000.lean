-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegree_F000
-- name    : LevyStochCalc_Poisson_SimpleChaosDegree_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:16:35.561612+00:00
-- url     : https://prove2.me/theorems/0b42dd35-9fe5-40bb-bfaf-b608144f0995
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleChaosDegree
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleChaosDegree. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F003
import Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F004
import Mathlib.Data.Nat.Choose.Multinomial

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

/-- The degree-`s` chaos element of a finite family of regions carried by a profile constant on
each region: the multinomial combination of the chaos elements of the multi-degrees of total
degree `s`. -/
noncomputable def markedChaosDegree (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
    (Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k) * poissonChaosProd N α B ω
/-- The degree-zero element is `1`. -/
@[simp] lemma markedChaosDegree_zero (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℝ) (ω : Ω) :
    markedChaosDegree N 0 B c ω = 1 := by
  rw [markedChaosDegree, Finset.piAntidiag_zero]
  simp [Nat.multinomial, poissonChaosProd]
/-! ### Measurability, integrability and the Gram -/

/-! ### A one-region family and strips -/

/-! ### The degree-two element -/

end LevyStochCalc.Poisson


