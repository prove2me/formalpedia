-- Prove2me | Definitions.Def_SourceProof_fe5db6d67c3dd41f9cc61a9c
-- name    : SourceProof_fe5db6d67c3dd41f9cc61a9c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:29:22.524319+00:00
-- url     : https://prove2.me/theorems/7ae920ea-eeda-4d22-a7e5-14baca1f0241
-- title:
--   LevyStochCalc source module: SourceProof_fe5db6d67c3dd41f9cc61a9c
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.sum_piAntidiag_multinomial_sq` comes from the `LevyStochCalc.Poisson.SimpleChaosDegree` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_fe5db6d67c3dd41f9cc61a9c {R : Type*} [CommSemiring R] {p : ℕ} (s : ℕ)
    (x : Fin p → R) :
    ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
        (Nat.multinomial Finset.univ α : R) * (Nat.multinomial Finset.univ α : R)
          * (∏ k, ((α k).factorial : R)) * ∏ k, x k ^ α k
      = (s.factorial : R) * (∑ k, x k) ^ s := by
  rw [Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin p)) x s, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hs : ∑ k, α k = s := (Finset.mem_piAntidiag.1 hα).1
  have hspec : (∏ k, ((α k).factorial : R)) * (Nat.multinomial Finset.univ α : R)
      = (s.factorial : R) := by
    have hsp := Nat.multinomial_spec (Finset.univ : Finset (Fin p)) α
    have := congrArg (fun n : ℕ => (n : R)) hsp
    push_cast at this
    rw [this, hs]
  calc (Nat.multinomial Finset.univ α : R) * (Nat.multinomial Finset.univ α : R)
        * (∏ k, ((α k).factorial : R)) * ∏ k, x k ^ α k
      = ((∏ k, ((α k).factorial : R)) * (Nat.multinomial Finset.univ α : R))
          * ((Nat.multinomial Finset.univ α : R) * ∏ k, x k ^ α k) := by ring
    _ = (s.factorial : R) * ((Nat.multinomial Finset.univ α : R) * ∏ k, x k ^ α k) := by
        rw [hspec]
/-! ### The degree-`s` element of a mark profile -/

/-! ### Measurability, integrability and the Gram -/

/-! ### A one-region family and strips -/

/-! ### The degree-two element -/

end LevyStochCalc.Poisson


