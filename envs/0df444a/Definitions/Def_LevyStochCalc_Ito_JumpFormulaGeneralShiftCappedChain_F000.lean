-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F000
-- name    : LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:36:14.354301+00:00
-- url     : https://prove2.me/theorems/4e7a0c29-5b04-47e4-b0ec-f1d81c43a5bd
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaGeneralShiftCappedChain
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaGeneralShiftCappedChain. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F002
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F002
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingLeftLim_F000

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

/-- The pathwise sum of the jumps carried by the mark set `A` over the window `(0, t]`, with the
jump coefficient evaluated along the path of states `Y`. -/
noncomputable def jumpSumAt (_X : Setting.JumpDiffusion W N coeffs x₀)
    (Y : ℝ → Ω → Fin n → ℝ) (A : Set E) (t : ℝ) (ω : Ω) (i : Fin n) : ℝ :=
  ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (Y q.1 ω) q.2 i ∂(N.N ω)
/-- Along the path itself the prescribed-path jump sum is the point-evaluated jump sum. -/
theorem jumpSumAt_path (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) :
    jumpSumAt X X.X A = JumpSplitting.jumpSum X A := rfl
/-- Along the left limits the prescribed-path jump sum is the left-limit jump sum. -/
theorem jumpSumAt_leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) :
    jumpSumAt X (JumpSplitting.leftLimPath X) A = JumpSplitting.jumpSumLeft X A := rfl
/-- The prescribed-path jump sum over the degenerate window vanishes. -/
theorem jumpSumAt_zero (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ)
    (A : Set E) (ω : Ω) (i : Fin n) : jumpSumAt X Y A 0 ω i = 0 := by
  simp [jumpSumAt]
/-- The jumps of a mark set accumulated up to the `k`-th arrival time capped at the horizon, with
the jump coefficient evaluated along the path of states `Y`. -/
noncomputable def cappedJumpSumAt (X : Setting.JumpDiffusion W N coeffs x₀)
    (Y : ℝ → Ω → Fin n → ℝ) (A : Set E) (T : ℝ) (k : ℕ) (ω : Ω) : Fin n → ℝ :=
  jumpSumAt X Y A
    (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Poisson.jumpTime N A k) T ω) ω
/-- Along the path itself the prescribed-path capped jump sum is the point-evaluated one. -/
theorem cappedJumpSumAt_path (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) :
    cappedJumpSumAt X X.X A = cappedJumpSum X A := rfl
/-- Along the left limits the prescribed-path capped jump sum reads the jump coefficient at the
left limits of the path. -/
theorem cappedJumpSumAt_leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E)
    (T : ℝ) (k : ℕ) (ω : Ω) :
    cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω
      = JumpSplitting.jumpSumLeft X A
          (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Poisson.jumpTime N A k) T ω) ω :=
  rfl
end Defs

section GeneralShift

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) (A : Set E)

/-- The capped jump sum at the zeroth arrival time vanishes. -/
theorem cappedJumpSumAt_zero {T : ℝ} (hT : 0 ≤ T) (ω : Ω) :
    cappedJumpSumAt X Y A T 0 ω = 0 := by
  funext i
  rw [cappedJumpSumAt,
    LevyStochCalc.Brownian.Ito.clipTime_eq_zero hT (LevyStochCalc.Poisson.jumpTime_zero N A ω),
    jumpSumAt_zero]
  rfl
/-- Past the horizon the capped jump sum is the jump sum over the whole window. -/
theorem cappedJumpSumAt_of_le {T : ℝ} {k : ℕ} {ω : Ω}
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    cappedJumpSumAt X Y A T k ω = jumpSumAt X Y A T ω := by
  rw [cappedJumpSumAt, LevyStochCalc.Brownian.Ito.clipTime_of_le hk]
/-- Past the horizon the capped jump sum no longer moves with the index. -/
theorem cappedJumpSumAt_succ_eq {T : ℝ} {k : ℕ} {ω : Ω}
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    cappedJumpSumAt X Y A T (k + 1) ω = cappedJumpSumAt X Y A T k ω := by
  rw [cappedJumpSumAt_of_le X Y A hk,
    cappedJumpSumAt_of_le X Y A
      (hk.trans (LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω))]
/-- Past the horizon the telescope's jump term vanishes. -/
theorem jumpTermAt_eq_zero_of_le {T : ℝ} {k : ℕ} {ω : Ω} (f : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ)
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    f (y + cappedJumpSumAt X Y A T (k + 1) ω) - f (y + cappedJumpSumAt X Y A T k ω) = 0 := by
  rw [cappedJumpSumAt_succ_eq X Y A hk, sub_self]
/-- The chain of capped shifts reaches the whole jump sum at any index whose arrival time has
passed the horizon, so a path that splits at the horizon is the translated Itô path there. -/
theorem eq_add_cappedJumpSumAt_of_le {T : ℝ} {m : ℕ} {ω : Ω} {V : ℝ → Ω → Fin n → ℝ}
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω)
    (hsplit : ∀ i : Fin n, X.X T ω i = V T ω i + jumpSumAt X Y A T ω i) (i : Fin n) :
    V T ω i + cappedJumpSumAt X Y A T m ω i = X.X T ω i := by
  rw [cappedJumpSumAt_of_le X Y A hm, hsplit i]
end GeneralShift

section MarkIdentification

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

end MarkIdentification

section CappedChain

variable {A : Set E}

end CappedChain

end LevyStochCalc.Ito.JumpFormula


