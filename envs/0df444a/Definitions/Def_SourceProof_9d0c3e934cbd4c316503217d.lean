-- Prove2me | Definitions.Def_SourceProof_9d0c3e934cbd4c316503217d
-- name    : SourceProof_9d0c3e934cbd4c316503217d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:42.075538+00:00
-- url     : https://prove2.me/theorems/e41ddb42-b1cb-4f84-a0f4-07100e0c1304
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.integral_sq_initial_add_discreteStochasticIntegral_le

import Definitions.Def_SourceProof_474b142ff5d9ac0d15a4d3a9
import Definitions.Def_SourceProof_9338c20a7c823520a42b860f
import Definitions.Def_SourceProof_ba14d06a4b8f2834583ab035
import Definitions.Def_SourceProof_d32c287b59bc71748a1634cd

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
theorem _root_.Prove2MeSourceProof.h_9d0c3e934cbd4c316503217d
    (hM : Martingale M F P) (hlp : ∀ n, MemLp (M n) 2 P)
    (hH : IsStronglyPredictable F H) (C : ℝ≥0)
    (hb : ∀ n, ∀ᵐ ω ∂P, ‖H n ω‖ ≤ C)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[F 0] Z) (hZlp : MemLp Z 2 P)
    (hZb : ∀ᵐ ω ∂P, (Z ω) ^ 2 ≤ (C : ℝ) ^ 2 * (M 0 ω) ^ 2) (n : ℕ) :
    ∫ ω, (Z ω + MeasureTheory.discreteStochasticIntegral H M n ω) ^ 2 ∂P ≤
      (C : ℝ) ^ 2 * ∫ ω, (M n ω) ^ 2 ∂P := by
  rw [(_root_.Prove2MeSourceProof.h_ba14d06a4b8f2834583ab035 hM) hlp hH
    (fun k ↦ ⟨C, hb k⟩) hZ hZlp]
  have hZi : (∫ ω, (Z ω) ^ 2 ∂P) ≤ (C : ℝ) ^ 2 * ∫ ω, (M 0 ω) ^ 2 ∂P := by
    rw [← integral_const_mul]
    exact integral_mono_ae hZlp.integrable_sq ((hlp 0).integrable_sq.const_mul _) hZb
  have hIi := (_root_.Prove2MeSourceProof.h_474b142ff5d9ac0d15a4d3a9 hM) hlp hH C hb n
  have heq := (_root_.Prove2MeSourceProof.h_9338c20a7c823520a42b860f hM) hlp n
  rw [(_root_.Prove2MeSourceProof.h_d32c287b59bc71748a1634cd hM) hlp n] at heq
  rw [← heq] at hIi
  nlinarith
end Martingale

end MeasureTheory


