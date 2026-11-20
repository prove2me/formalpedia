-- Prove2me | Definitions.Def_SourceProof_c802439593f5dcb38e4f6740
-- name    : SourceProof_c802439593f5dcb38e4f6740
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:28:40.957492+00:00
-- url     : https://prove2.me/theorems/19d6e9c4-7a79-4cdf-afa9-ee24ba2faa7f
-- title:
--   LevyStochCalc source module: SourceProof_c802439593f5dcb38e4f6740
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.exists_pairIndex_of_mem_piAntidiag_two` comes from the `LevyStochCalc.Poisson.SimpleChaosDegree` module. The staged Lean declaration includes its source proof and dependency references.
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

/-! ### Measurability, integrability and the Gram -/

/-! ### A one-region family and strips -/

/-! ### The degree-two element -/


theorem _root_.Prove2MeSourceProof.h_c802439593f5dcb38e4f6740 {p : ℕ} {α : Fin p → ℕ}
    (hα : α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) 2) :
    ∃ k l : Fin p, α = pairIndex k l := by
  classical
  have hs : ∑ j, α j = 2 := (Finset.mem_piAntidiag.1 hα).1
  have hone : ∀ k : Fin p, α k ≤ 2 := fun k =>
    le_of_le_of_eq (Finset.single_le_sum (f := α) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ k)) hs
  have hpair : ∀ {k l : Fin p}, k ≠ l → α k + α l ≤ 2 := by
    intro k l hkl
    have hle := Finset.sum_le_sum_of_subset (f := α)
      (Finset.subset_univ ({k, l} : Finset (Fin p)))
    rw [Finset.sum_pair hkl] at hle
    omega
  have htriple : ∀ {k l j : Fin p}, k ≠ l → k ≠ j → l ≠ j →
      α k + α l + α j ≤ 2 := by
    intro k l j hkl hkj hlj
    have hle := Finset.sum_le_sum_of_subset (f := α)
      (Finset.subset_univ ({k, l, j} : Finset (Fin p)))
    rw [Finset.sum_insert (by simp [hkl, hkj]), Finset.sum_pair hlj] at hle
    omega
  obtain ⟨k, hk⟩ : ∃ k, α k ≠ 0 := by
    by_contra hcon
    have hz : ∑ j, α j = 0 :=
      Finset.sum_eq_zero fun j _ => not_not.1 fun h => hcon ⟨j, h⟩
    omega
  have hk2 := hone k
  rcases (by omega : α k = 2 ∨ α k = 1) with h2 | h1
  · refine ⟨k, k, funext fun j => ?_⟩
    rcases eq_or_ne j k with rfl | hj
    · rw [h2, show LevyStochCalc.Poisson.pairIndex j j j = 2 by simp [LevyStochCalc.Poisson.pairIndex]]
    · have := hpair (k := k) (l := j) (Ne.symm hj)
      have hzj : α j = 0 := by omega
      rw [hzj]
      simp [LevyStochCalc.Poisson.pairIndex, hj]
  · have hrest : ∑ j ∈ Finset.univ.erase k, α j = 1 := by
      have hsplit : α k + ∑ j ∈ Finset.univ.erase k, α j = ∑ j, α j :=
        Finset.add_sum_erase Finset.univ α (Finset.mem_univ k)
      omega
    obtain ⟨l, hlmem, hl⟩ : ∃ l ∈ Finset.univ.erase k, α l ≠ 0 := by
      by_contra hcon
      have := Finset.sum_eq_zero (s := Finset.univ.erase k) (f := α)
        fun j hj => not_not.1 fun h => hcon ⟨j, hj, h⟩
      omega
    have hlk : l ≠ k := (Finset.mem_erase.1 hlmem).1
    have hl1 : α l = 1 := by
      have := hpair (k := k) (l := l) (Ne.symm hlk)
      omega
    refine ⟨k, l, funext fun j => ?_⟩
    rcases eq_or_ne j k with rfl | hjk
    · rw [h1]
      simp [LevyStochCalc.Poisson.pairIndex, Ne.symm hlk]
    · rcases eq_or_ne j l with rfl | hjl
      · rw [hl1]
        simp [LevyStochCalc.Poisson.pairIndex, hjk]
      · have := htriple (k := k) (l := l) (j := j) (Ne.symm hlk) (Ne.symm hjk) (Ne.symm hjl)
        have hzj : α j = 0 := by omega
        rw [hzj]
        simp [LevyStochCalc.Poisson.pairIndex, hjk, hjl]
end LevyStochCalc.Poisson


