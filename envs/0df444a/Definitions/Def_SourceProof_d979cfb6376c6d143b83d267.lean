-- Prove2me | Definitions.Def_SourceProof_d979cfb6376c6d143b83d267
-- name    : SourceProof_d979cfb6376c6d143b83d267
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:47:13.397085+00:00
-- url     : https://prove2.me/theorems/97791840-0db4-4bb7-9693-a47b855aab09
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Ito.JumpFormula.ae_forall_jumpSumAt_eq_cappedJumpSumAt
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

end MarkIdentification

section CappedChain

variable {A : Set E}


theorem _root_.Prove2MeSourceProof.h_d979cfb6376c6d143b83d267
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      ∀ i : Fin n, jumpSumAt X Y A s ω i = cappedJumpSumAt X Y A T k ω i := by
  classical
  filter_upwards [_root_.Prove2MeSourceProof.h_2d73a2b6df3c10b500c2eec5 N A hA hAν T]
    with ω hω
  obtain ⟨K, θ, ε, -, hrange, hmem, hsum⟩ := hω
  intro k s h1 h2 i
  have hkT : LevyStochCalc.Poisson.jumpTime N A k ω < ((T : ℝ) : WithTop ℝ) := by
    by_contra hcon
    have hk : LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T k ω = ((T : ℝ) : WithTop ℝ) :=
      min_eq_right (not_lt.mp hcon)
    have hk1 : LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T (k + 1) ω = ((T : ℝ) : WithTop ℝ) :=
      min_eq_right ((not_lt.mp hcon).trans
        (LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω))
    rw [hk] at h1
    rw [hk1] at h2
    exact absurd (h1.trans h2) (lt_irrefl _)
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp
    (lt_trans hkT (WithTop.coe_lt_top T)).ne
  have hqT : q < T := by
    have := hkT
    rw [← hq] at this
    exact_mod_cast this
  have hkeq : LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T k ω = ((q : ℝ) : WithTop ℝ) := by
    rw [LevyStochCalc.Ito.JumpFormula.cappedJumpTime, ← hq, min_eq_left (le_of_lt (by exact_mod_cast hqT))]
  have hqs : q < s := by
    rw [hkeq] at h1
    exact_mod_cast h1
  have hsucc : ((s : ℝ) : WithTop ℝ) < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω :=
    lt_of_lt_of_le h2 (min_le_left _ _)
  have hsT : s ≤ T := by
    have := lt_of_lt_of_le h2 (min_le_right _ _)
    exact le_of_lt (by exact_mod_cast this)
  have hqT' : q ≤ T := le_of_lt hqT
  have hcap : LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt X Y A T k ω i = LevyStochCalc.Ito.JumpFormula.jumpSumAt X Y A q ω i := by
    rw [LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm,
      min_eq_right hqT']
  have hkey : ∀ j : Fin K, θ j ≤ s ↔ θ j ≤ q := by
    intro j
    constructor
    · intro hjs
      have hmemj : θ j ∈ Set.range θ := Set.mem_range_self j
      rw [hrange] at hmemj
      obtain ⟨i', hi', -, -⟩ := hmemj
      rcases le_or_gt i' k with hik | hik
      · have := LevyStochCalc.Poisson.jumpTime_mono N A hik ω
        rw [hi', ← hq] at this
        exact_mod_cast this
      · have := LevyStochCalc.Poisson.jumpTime_mono N A (Nat.succ_le_of_lt hik) ω
        rw [hi'] at this
        exact absurd (lt_of_lt_of_le hsucc this) (not_lt.mpr (by exact_mod_cast hjs))
    · intro hjq
      exact le_of_lt (lt_of_le_of_lt hjq hqs)
  rw [hcap, _root_.Prove2MeSourceProof.h_4574c5c52c160c5cb88ceea7 X Y hA hmem hsum hsT i,
    _root_.Prove2MeSourceProof.h_4574c5c52c160c5cb88ceea7 X Y hA hmem hsum hqT' i]
  exact Finset.sum_congr rfl fun j _ => by
    by_cases hj : θ j ≤ s
    · rw [if_pos hj, if_pos ((hkey j).mp hj)]
    · rw [if_neg hj, if_neg (fun hc => hj ((hkey j).mpr hc))]
end CappedChain

end LevyStochCalc.Ito.JumpFormula


