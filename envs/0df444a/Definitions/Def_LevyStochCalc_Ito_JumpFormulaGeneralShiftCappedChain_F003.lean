-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F003
-- name    : LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:51:05.99717+00:00
-- url     : https://prove2.me/theorems/aaca1f64-0f60-432e-80d1-43889fe67e2b
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaGeneralShiftCappedChain
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaGeneralShiftCappedChain. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F002
import Definitions.Def_SourceProof_d979cfb6376c6d143b83d267

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

/-- **The piecewise translation between consecutive capped arrival times.** Strictly between
consecutive capped arrival times a path splitting into a continuous part and the jump sum along
a prescribed path of states is that continuous part translated by the capped jump sum. -/
theorem ae_forall_add_cappedJumpSumAt_eq_of_path
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    {X : Setting.JumpDiffusion W N coeffs x₀} {Y Z : ℝ → Ω → Fin n → ℝ}
    {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + jumpSumAt X Y A t ω i)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X Y A T k ω = Z s ω :=
  add_shift_eq_of_ae_forall_at_of_path hsplit
    (cappedJumpTime_zero N A hT) (cappedJumpTime_le_succ N A T)
    (_root_.Prove2MeSourceProof.h_d979cfb6376c6d143b83d267 X Y hA hAν T)
/-- **The piecewise translation between consecutive capped arrival times of a jump diffusion.**
Strictly between consecutive capped arrival times the jump path is the continuous part translated
by the capped jump sum evaluated along the prescribed path of states. -/
theorem ae_forall_add_cappedJumpSumAt_eq
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    {X : Setting.JumpDiffusion W N coeffs x₀} {Y : ℝ → Ω → Fin n → ℝ}
    {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSumAt X Y A t ω i)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X Y A T k ω = X.X s ω :=
  ae_forall_add_cappedJumpSumAt_eq_of_path hsplit hA hAν hT
end CappedChain

end LevyStochCalc.Ito.JumpFormula


