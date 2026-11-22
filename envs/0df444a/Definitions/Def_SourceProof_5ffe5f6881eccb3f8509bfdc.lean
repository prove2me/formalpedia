-- Prove2me | Definitions.Def_SourceProof_5ffe5f6881eccb3f8509bfdc
-- name    : SourceProof_5ffe5f6881eccb3f8509bfdc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:45:49.141049+00:00
-- url     : https://prove2.me/theorems/575f0fd6-f970-40df-ab76-2ed1b7e68159
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_succ_eq_add_gamma
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F000
import Definitions.Def_SourceProof_4574c5c52c160c5cb88ceea7

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The capped jump chain over a prescribed evaluation path

The pathwise sum of the jumps carried by a mark set over a window reads the jump coefficient at a
prescribed path of states, and capping the arrival times at the horizon turns that sum into the
chain of jumps accumulated up to each arrival time. Over an enumeration of the atoms of the
window the jump sum is the sum of the jump coefficient over the enumerated atoms whose times lie
in the sub-window, so the capped sum gains exactly the jump coefficient carried by each arrival
time inside the window and does not move strictly between consecutive arrival times; a path that
splits at all nonnegative times into a continuous part and that jump sum is therefore the
continuous part translated by the capped jump sum on each such interval.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section Defs

end Defs

section GeneralShift

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) (A : Set E)

end GeneralShift

section MarkIdentification

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}


theorem _root_.Prove2MeSourceProof.h_5ffe5f6881eccb3f8509bfdc (hA : MeasurableSet A)
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
      cappedJumpSumAt X Y A T (k + 1) ω
        = cappedJumpSumAt X Y A T k ω + coeffs.γ (θ j) (Y (θ j) ω) (ε j) := by
  classical
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
  have hmemr : r ∈ Set.range θ := by
    rw [hrange]
    exact ⟨k + 1, hr.symm, hr0, hrT⟩
  obtain ⟨j₀, hj₀⟩ := hmemr
  refine ⟨j₀, by rw [← hr, hj₀], ?_⟩
  have hck1 : LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt X Y A T (k + 1) ω = LevyStochCalc.Ito.JumpFormula.jumpSumAt X Y A r ω := by
    rw [LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt, LevyStochCalc.Brownian.Ito.clipTime_eq_min hr.symm, min_eq_right hrT]
  have hck : LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt X Y A T k ω = LevyStochCalc.Ito.JumpFormula.jumpSumAt X Y A q ω := by
    rw [LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm, min_eq_right hqT]
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
  have h1 := _root_.Prove2MeSourceProof.h_4574c5c52c160c5cb88ceea7 X Y hA hmem hsum hrT i
  have h2 := _root_.Prove2MeSourceProof.h_4574c5c52c160c5cb88ceea7 X Y hA hmem hsum hqT i
  have hdiff : LevyStochCalc.Ito.JumpFormula.jumpSumAt X Y A r ω i - LevyStochCalc.Ito.JumpFormula.jumpSumAt X Y A q ω i
      = coeffs.γ (θ j₀) (Y (θ j₀) ω) (ε j₀) i := by
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

section CappedChain

variable {A : Set E}

end CappedChain

end LevyStochCalc.Ito.JumpFormula


