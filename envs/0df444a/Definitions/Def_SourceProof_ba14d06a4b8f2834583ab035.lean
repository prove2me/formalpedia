-- Prove2me | Definitions.Def_SourceProof_ba14d06a4b8f2834583ab035
-- name    : SourceProof_ba14d06a4b8f2834583ab035
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:00:33.224093+00:00
-- url     : https://prove2.me/theorems/460421ad-5e65-5fd6-9232-f34d52dba406
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.integral_sq_initial_add_discreteStochasticIntegral

import Definitions.Def_SourceProof_94b26ceff87499d497c994b8
import Definitions.Def_SourceProof_c16ea08a09c28425ded13bd1
import Definitions.Def_SourceProof_d32c287b59bc71748a1634cd
import Definitions.Def_SourceProof_eae059fb1d843e68f8ce3b08

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
theorem _root_.Prove2MeSourceProof.h_ba14d06a4b8f2834583ab035
    (hM : Martingale M F P) (hlp : ∀ n, MemLp (M n) 2 P)
    (hH : IsStronglyPredictable F H) (hb : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂P, ‖H n ω‖ ≤ C)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[F 0] Z) (hZlp : MemLp Z 2 P) (n : ℕ) :
    ∫ ω, (Z ω + MeasureTheory.discreteStochasticIntegral H M n ω) ^ 2 ∂P =
      (∫ ω, (Z ω) ^ 2 ∂P) + ∫ ω, (MeasureTheory.discreteStochasticIntegral H M n ω) ^ 2 ∂P := by
  let I := MeasureTheory.discreteStochasticIntegral H M
  have hI : Martingale I F P := (_root_.Prove2MeSourceProof.h_eae059fb1d843e68f8ce3b08 hM) hH hb
  have hIlp : ∀ n, MemLp (I n) 2 P := _root_.Prove2MeSourceProof.h_94b26ceff87499d497c994b8 hlp hH hb
  let N : ℕ → Ω → ℝ := fun n ω ↦ Z ω + I n ω
  have hN : Martingale N F P :=
    (martingale_const_fun F P hZ (hZlp.integrable (by norm_num))).add hI
  have hNlp : ∀ n, MemLp (N n) 2 P := fun n ↦ hZlp.add (hIlp n)
  have hQV : MeasureTheory.pathwiseQuadraticVariation N n = MeasureTheory.pathwiseQuadraticVariation I n := by
    funext ω
    apply sum_congr rfl
    intro k _
    change ((Z ω + I (k + 1) ω) - (Z ω + I k ω)) ^ 2 = _
    rw [add_sub_add_left_eq_sub]
  have heq := (_root_.Prove2MeSourceProof.h_d32c287b59bc71748a1634cd hN) hNlp n
  rw [hQV, (_root_.Prove2MeSourceProof.h_d32c287b59bc71748a1634cd hI) hIlp n] at heq
  have hI0 : I 0 = 0 := _root_.Prove2MeSourceProof.h_c16ea08a09c28425ded13bd1 H M
  have hN0 : N 0 = Z := by simp only [N, hI0, Pi.zero_apply, add_zero]
  rw [hI0, hN0] at heq
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    integral_zero, sub_zero] at heq
  change _ = (∫ ω, (Z ω + I n ω) ^ 2 ∂P) - _ at heq
  linarith
end Martingale

end MeasureTheory


