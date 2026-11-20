-- Prove2me | Definitions.Def_SourceProof_1dd703ef30b98a779e073f75
-- name    : SourceProof_1dd703ef30b98a779e073f75
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:26:24.514838+00:00
-- url     : https://prove2.me/theorems/c1345fe1-e335-4d9c-9413-cd1dd5e4a314
-- title:
--   LevyStochCalc source module: SourceProof_1dd703ef30b98a779e073f75
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.piAntidiag_univ_one` comes from the `LevyStochCalc.Poisson.SimpleChaosDegree` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_1dd703ef30b98a779e073f75 (p : ℕ) :
    Finset.piAntidiag (Finset.univ : Finset (Fin p)) 1
      = Finset.image (fun k : Fin p => Pi.single k 1) Finset.univ := by
  classical
  ext α
  simp only [Finset.mem_piAntidiag, Finset.mem_image, Finset.mem_univ, true_and, ne_eq,
    implies_true, and_true]
  constructor
  · intro hs
    have hs1 : ∑ j, α j = 1 := hs
    obtain ⟨k, hk⟩ : ∃ k, α k = 1 := by
      by_contra hcon
      have hz : ∀ k : Fin p, α k = 0 := by
        intro k
        have hle : α k ≤ ∑ j, α j :=
          Finset.single_le_sum (f := α) (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
        have hne : α k ≠ 1 := fun h => hcon ⟨k, h⟩
        omega
      have hzero : ∑ j, α j = 0 := Finset.sum_eq_zero fun j _ => hz j
      omega
    refine ⟨k, ?_⟩
    funext j
    rcases eq_or_ne j k with rfl | hj
    · simp [hk]
    · have hj' : j ∈ Finset.univ.erase k := Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩
      have hsplit : α k + ∑ i ∈ Finset.univ.erase k, α i = ∑ i, α i :=
        Finset.add_sum_erase Finset.univ α (Finset.mem_univ k)
      have hsub : α j ≤ ∑ i ∈ Finset.univ.erase k, α i :=
        Finset.single_le_sum (f := α) (fun i _ => Nat.zero_le _) hj'
      have hzj : α j = 0 := by omega
      simp [Pi.single_eq_of_ne hj, hzj]
  · rintro ⟨k, rfl⟩
    simp
/-! ### Measurability, integrability and the Gram -/

/-! ### A one-region family and strips -/

/-! ### The degree-two element -/

end LevyStochCalc.Poisson


