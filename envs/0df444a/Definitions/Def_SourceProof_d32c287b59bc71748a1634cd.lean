-- Prove2me | Definitions.Def_SourceProof_d32c287b59bc71748a1634cd
-- name    : SourceProof_d32c287b59bc71748a1634cd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:31.4699+00:00
-- url     : https://prove2.me/theorems/023e8ecf-387c-4ecd-8074-5ec69ce18fcf
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.integral_pathwiseQuadraticVariation_eq_integral_sq_sub_initial_sq

import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F002
import Definitions.Def_SourceProof_442b482eafb28142fd8f3cea
import Definitions.Def_SourceProof_549506abde5375992c159de2
import Definitions.Def_SourceProof_8ea11dc318d9dadc642df2e6
import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # L2 estimates retaining the initial term

An initial, time-zero measurable square-integrable value is orthogonal to the future
predictable integral. The resulting estimate includes the source initial contribution.
-/

@[expose] public section

open Filter Finset
open scoped NNReal ENNReal BigOperators

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℕ mΩ} {M H : ℕ → Ω → ℝ}
  [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

namespace Martingale
theorem _root_.Prove2MeSourceProof.h_d32c287b59bc71748a1634cd
    (hM : Martingale M F P) (hlp : ∀ n, MemLp (M n) 2 P) (n : ℕ) :
    ∫ ω, pathwiseQuadraticVariation M n ω ∂P =
      (∫ ω, (M n ω) ^ 2 ∂P) - ∫ ω, (M 0 ω) ^ 2 ∂P := by
  have heq := ((_root_.Prove2MeSourceProof.h_549506abde5375992c159de2 hM) hlp).setIntegral_eq
    (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  simp only [Measure.restrict_univ, MeasureTheory.squareMinusPathwiseQuadraticVariation,
    _root_.Prove2MeSourceProof.h_442b482eafb28142fd8f3cea, sub_zero] at heq
  change (∫ ω, (M 0 ω) ^ 2 ∂P) = ∫ ω, (M n ω) ^ 2 - MeasureTheory.pathwiseQuadraticVariation M n ω ∂P at heq
  rw [integral_sub (hlp n).integrable_sq
    (_root_.Prove2MeSourceProof.h_8ea11dc318d9dadc642df2e6
      (fun k ↦ ((hlp (k + 1)).sub (hlp k)).integrable_sq) n)] at heq
  linarith
end Martingale

end MeasureTheory


