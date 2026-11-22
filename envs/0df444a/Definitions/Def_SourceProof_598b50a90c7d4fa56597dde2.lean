-- Prove2me | Definitions.Def_SourceProof_598b50a90c7d4fa56597dde2
-- name    : SourceProof_598b50a90c7d4fa56597dde2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:07:34.649716+00:00
-- url     : https://prove2.me/theorems/cff3b5bf-b216-44d2-a98b-269b1766e545
-- title:
--   LevyStochCalc source module: SourceProof_598b50a90c7d4fa56597dde2
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.cappedJumpSum_succ_eq_add_gamma` comes from the `LevyStochCalc.Ito.JumpFormulaFiniteActivityExhaustion` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F000
import Definitions.Def_SourceProof_1ccbf94d189a78e3d3f14cc3

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exhausting a finite-activity jump path by its arrival times

The jumps of a mark set accumulated up to the arrival times capped at the horizon no longer move
once the arrival time has passed the horizon, so a telescope over a chain of arrival times has
only in-window terms, and the in-window members of such a chain are matched one for one with the
entries of the strictly monotone enumeration of the window's atom times. On a mark set of finite
intensity almost every path has an arrival time beyond the horizon, so an identity holding almost
everywhere on each event where the chain has passed the horizon holds almost everywhere. Between
consecutive arrival times inside the window the accumulated jumps gain exactly the jump
coefficient carried by the later arrival time and the mark enumerated with it, and the progressive
measurability of the chain data and of the integrands passes to the right-continuous
regularisation of a filtration.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section CappedShift

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) (A : Set E)

end CappedShift

section Reindex

end Reindex

section RightContinuous

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end RightContinuous

section Exhaustion

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (A : Set E)

end Exhaustion

section MarkIdentification

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}


theorem _root_.Prove2MeSourceProof.h_598b50a90c7d4fa56597dde2 (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hθ : Function.Injective θ)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    {k : ℕ}
    (hlt : LevyStochCalc.Poisson.jumpTime N A k ω
      < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω)
    (hle : LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ)) :
    ∃ j : Fin K, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω = ((θ j : ℝ) : WithTop ℝ) ∧
      cappedJumpSum X A T (k + 1) ω
        = cappedJumpSum X A T k ω + coeffs.γ (θ j) (X.X (θ j) ω) (ε j) := by
  classical
  -- The two arrival times are finite reals `q < r ≤ T`, with `0 ≤ q`.
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp
    (hle.trans_lt (WithTop.coe_lt_top T)).ne
  have hkle : LevyStochCalc.Poisson.jumpTime N A k ω ≤ ((r : ℝ) : WithTop ℝ) := by
    rw [hr]; exact hlt.le
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp
    (lt_of_le_of_lt hkle (WithTop.coe_lt_top r)).ne
  have hqr : q < r := by
    have := hlt
    rw [← hq, ← hr] at this
    exact_mod_cast this
  have hrT : r ≤ T := by
    have := hle
    rw [← hr] at this
    exact_mod_cast this
  have hq0 : (0 : ℝ) ≤ q := by
    have := LevyStochCalc.Poisson.coe_zero_le_jumpTime N A k ω
    rw [← hq] at this
    exact_mod_cast this
  have hqT : q ≤ T := le_of_lt (lt_of_lt_of_le hqr hrT)
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt hq0 hqr
  -- The later arrival time is one of the enumerated atom times.
  have hmemr : r ∈ Set.range θ := by
    rw [hrange]
    exact ⟨k + 1, hr.symm, hr0, hrT⟩
  obtain ⟨j₀, hj₀⟩ := hmemr
  refine ⟨j₀, by rw [← hr, hj₀], ?_⟩
  -- The two capped shifts are the jump sums at `r` and at `q`.
  have hck1 : LevyStochCalc.Ito.JumpFormula.cappedJumpSum X A T (k + 1) ω
      = LevyStochCalc.Ito.JumpSplitting.jumpSum X A r ω := by
    rw [LevyStochCalc.Ito.JumpFormula.cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_eq_min hr.symm, min_eq_right hrT]
  have hck : LevyStochCalc.Ito.JumpFormula.cappedJumpSum X A T k ω = LevyStochCalc.Ito.JumpSplitting.jumpSum X A q ω := by
    rw [LevyStochCalc.Ito.JumpFormula.cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm, min_eq_right hqT]
  -- Only the atom at the later arrival time enters the increment.
  have hkey : ∀ j : Fin K, j ≠ j₀ → (θ j ≤ r ↔ θ j ≤ q) := by
    intro j hj
    constructor
    · intro hjr
      have hmemj : θ j ∈ Set.range θ := Set.mem_range_self j
      rw [hrange] at hmemj
      obtain ⟨i, hi, -, -⟩ := hmemj
      rcases le_or_gt i k with hik | hik
      · have := LevyStochCalc.Poisson.jumpTime_mono N A hik ω
        rw [hi, ← hq] at this
        exact_mod_cast this
      · have := LevyStochCalc.Poisson.jumpTime_mono N A (Nat.succ_le_of_lt hik) ω
        rw [hi, ← hr] at this
        have hrj : r ≤ θ j := by exact_mod_cast this
        exact absurd (hθ (hj₀.trans (le_antisymm hrj hjr))).symm hj
    · intro hjq
      exact le_of_lt (lt_of_le_of_lt hjq hqr)
  funext i
  have h1 := _root_.Prove2MeSourceProof.h_1ccbf94d189a78e3d3f14cc3 X hA hmem hsum hrT i
  have h2 := _root_.Prove2MeSourceProof.h_1ccbf94d189a78e3d3f14cc3 X hA hmem hsum hqT i
  have hdiff : LevyStochCalc.Ito.JumpSplitting.jumpSum X A r ω i
      - LevyStochCalc.Ito.JumpSplitting.jumpSum X A q ω i
      = coeffs.γ (θ j₀) (X.X (θ j₀) ω) (ε j₀) i := by
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine (Finset.sum_eq_single j₀ ?_ ?_).trans ?_
    · intro j _ hj
      by_cases hjr : θ j ≤ r
      · rw [if_pos hjr, if_pos ((hkey j hj).mp hjr), sub_self]
      · rw [if_neg hjr, if_neg (fun hc => hjr ((hkey j hj).mpr hc)), sub_self]
    · intro hj
      exact absurd (Finset.mem_univ j₀) hj
    · rw [if_pos (le_of_eq hj₀), if_neg (by rw [hj₀]; exact not_le.mpr hqr), sub_zero]
  rw [hck1, hck]
  simp only [Pi.add_apply]
  linarith
end MarkIdentification

end LevyStochCalc.Ito.JumpFormula


