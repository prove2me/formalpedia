-- Prove2me | Definitions.Def_SourceProof_b233f14b4b88a4af49762008
-- name    : SourceProof_b233f14b4b88a4af49762008
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:56:11.374549+00:00
-- url     : https://prove2.me/theorems/78325a95-4b50-4261-9468-7faeaebaf79f
-- title:
--   LevyStochCalc source module: SourceProof_b233f14b4b88a4af49762008
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_succ_eq_of_horizon_lt` comes from the `LevyStochCalc.Ito.JumpFormulaGeneralShiftAtomSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The telescope's jump sum over a prescribed evaluation path

Over an enumeration of the atoms of a window, the telescope of a state function along the chain
of capped jump sums collapses to the sum, over those atoms, of the increments of the state
function taken at the left limits of the jump path and displaced by the jump coefficient read at
the prescribed states: an index whose arrival time has passed the horizon contributes nothing and
each in-window index contributes one increment. Almost surely every window carries such an
enumeration, which gives that identification for the path itself and for a path translated by the
jump sum, together with the piecewise translation and the atom sum for the jump sums evaluated at
the point values and at the left limits of the path.
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

section JumpSideAssembly

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}


theorem _root_.Prove2MeSourceProof.h_b233f14b4b88a4af49762008 (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    {k : ℕ} (hk : ((T : ℝ) : WithTop ℝ) < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω) :
    cappedJumpSumAt X Y A T (k + 1) ω = cappedJumpSumAt X Y A T k ω := by
  classical
  have h1 : LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt X Y A T (k + 1) ω = LevyStochCalc.Ito.JumpFormula.jumpSumAt X Y A T ω :=
    LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_of_le X Y A hk.le
  by_cases hkT : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω
  · rw [h1, LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_of_le X Y A hkT]
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp
      (lt_trans (not_le.mp hkT) (WithTop.coe_lt_top T)).ne
    have hqT : q < T := by
      have hlt := not_le.mp hkT
      rw [← hq] at hlt
      exact_mod_cast hlt
    have h2 : LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt X Y A T k ω = LevyStochCalc.Ito.JumpFormula.jumpSumAt X Y A q ω := by
      rw [LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm,
        min_eq_right (le_of_lt hqT)]
    rw [h1, h2]
    funext i
    rw [_root_.Prove2MeSourceProof.h_4574c5c52c160c5cb88ceea7 X Y hA hmem hsum le_rfl i,
      _root_.Prove2MeSourceProof.h_4574c5c52c160c5cb88ceea7 X Y hA hmem hsum (le_of_lt hqT) i]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hjq : θ j ≤ q := by
      have hmemj : θ j ∈ Set.range θ := Set.mem_range_self j
      rw [hrange] at hmemj
      obtain ⟨i', hi', -, hjT⟩ := hmemj
      rcases le_or_gt i' k with hik | hik
      · have hle := LevyStochCalc.Poisson.jumpTime_mono N A hik ω
        rw [hi', ← hq] at hle
        exact_mod_cast hle
      · have hge := LevyStochCalc.Poisson.jumpTime_mono N A (Nat.succ_le_of_lt hik) ω
        rw [hi'] at hge
        exact absurd (lt_of_lt_of_le hk hge) (not_lt.mpr (by exact_mod_cast hjT))
    rw [if_pos (hmem j).1.2, if_pos hjq]
end JumpSideAssembly

section MarkIdentificationAe

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

end MarkIdentificationAe

section Instances

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

end Instances

end LevyStochCalc.Ito.JumpFormula


