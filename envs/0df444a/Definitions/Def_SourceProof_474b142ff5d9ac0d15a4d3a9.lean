-- Prove2me | Definitions.Def_SourceProof_474b142ff5d9ac0d15a4d3a9
-- name    : SourceProof_474b142ff5d9ac0d15a4d3a9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:45:51.066351+00:00
-- url     : https://prove2.me/theorems/ac0bfb38-d2d4-457f-b977-0171e778b8e8
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.integral_sq_discreteStochasticIntegral_le

import Definitions.Def_SourceProof_15f823291c6a3c3a94b3df5f
import Definitions.Def_SourceProof_5cc80b9bfdcf1557ce8e5ae0
import Definitions.Def_SourceProof_8ea11dc318d9dadc642df2e6
import Definitions.Def_SourceProof_9338c20a7c823520a42b860f
import Definitions.Def_SourceProof_94b26ceff87499d497c994b8
import Definitions.Def_SourceProof_c16ea08a09c28425ded13bd1
import Definitions.Def_SourceProof_eae059fb1d843e68f8ce3b08

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # L2 isometry and estimates for discrete predictable integrals

These estimates will be reused on sampled stopping-time partitions. The integral and discrete
bracket are the existing canonical owners; no continuous-time bracket is introduced here.
-/

@[expose] public section

open Filter Finset
open scoped NNReal ENNReal BigOperators

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℕ mΩ} {M H : ℕ → Ω → ℝ}

variable [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

namespace Martingale

theorem _root_.Prove2MeSourceProof.h_474b142ff5d9ac0d15a4d3a9
    (hM : Martingale M F P) (hlp : ∀ n, MemLp (M n) 2 P)
    (hH : IsStronglyPredictable F H) (C : ℝ≥0)
    (hb : ∀ n, ∀ᵐ ω ∂P, ‖H n ω‖ ≤ C) (n : ℕ) :
    ∫ ω, (MeasureTheory.discreteStochasticIntegral H M n ω) ^ 2 ∂P ≤
      (C : ℝ) ^ 2 * ∫ ω, (M n ω - M 0 ω) ^ 2 ∂P := by
  have hIb : ∀ k, ∃ R : ℝ, ∀ᵐ ω ∂P, ‖H k ω‖ ≤ R := fun k ↦ ⟨(C : ℝ), hb k⟩
  have hIlp := _root_.Prove2MeSourceProof.h_94b26ceff87499d497c994b8 hlp hH hIb
  have hi : Integrable (MeasureTheory.pathwiseQuadraticVariation M n) P :=
    _root_.Prove2MeSourceProof.h_8ea11dc318d9dadc642df2e6 (fun k ↦ ((hlp (k + 1)).sub (hlp k)).integrable_sq) n
  have hIhi : Integrable
      (MeasureTheory.pathwiseQuadraticVariation (MeasureTheory.discreteStochasticIntegral H M) n) P :=
    _root_.Prove2MeSourceProof.h_8ea11dc318d9dadc642df2e6
      (fun k ↦ ((hIlp (k + 1)).sub (hIlp k)).integrable_sq) n
  have hpoint : ∀ᵐ ω ∂P,
      MeasureTheory.pathwiseQuadraticVariation (MeasureTheory.discreteStochasticIntegral H M) n ω ≤
        (C : ℝ) ^ 2 * MeasureTheory.pathwiseQuadraticVariation M n ω := by
    filter_upwards [ae_all_iff.mpr hb] with ω hω
    rw [_root_.Prove2MeSourceProof.h_15f823291c6a3c3a94b3df5f, MeasureTheory.pathwiseQuadraticVariation, mul_sum]
    apply sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs (H (k + 1) ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa only [Real.norm_eq_abs] using hω (k + 1)) 2
  calc
    _ = ∫ ω, MeasureTheory.pathwiseQuadraticVariation (MeasureTheory.discreteStochasticIntegral H M) n ω ∂P := by
      have hIm := (_root_.Prove2MeSourceProof.h_eae059fb1d843e68f8ce3b08 hM) hH hIb
      simpa only [_root_.Prove2MeSourceProof.h_c16ea08a09c28425ded13bd1, Pi.zero_apply, sub_zero] using
        ((_root_.Prove2MeSourceProof.h_9338c20a7c823520a42b860f hIm) hIlp n).symm
    _ ≤ ∫ ω, (C : ℝ) ^ 2 * MeasureTheory.pathwiseQuadraticVariation M n ω ∂P :=
      integral_mono_ae hIhi (hi.const_mul _) hpoint
    _ = (C : ℝ) ^ 2 * ∫ ω, (M n ω - M 0 ω) ^ 2 ∂P := by
      rw [integral_const_mul,
        (_root_.Prove2MeSourceProof.h_9338c20a7c823520a42b860f hM) hlp n]
end Martingale

end MeasureTheory


