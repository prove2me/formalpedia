-- Prove2me | Definitions.Def_SourceProof_77e3615cd5fb18090525a5f1
-- name    : SourceProof_77e3615cd5fb18090525a5f1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:49.802799+00:00
-- url     : https://prove2.me/theorems/bb731e45-e5af-4276-b8c6-365b6ca7f10e
-- title:
--   StochLean source theorem: MeasureTheory.uniformIntegrable_of_bounded_integral_sq

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_Function_DeLaValleePoussin_F001
import Definitions.Def_SourceProof_a4946c6794948bd9996bb99a
import Definitions.Def_SourceProof_e04f83f7c1e6a0d560fd2699
import Mathlib.MeasureTheory.Function.L2Space

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded second moments imply uniform integrability

This is a specialization of the existing superlinear-envelope theorem with
the actual square envelope, not an assumption about a limiting family.
-/

@[expose] public section

open Filter
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {f : ι → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_77e3615cd5fb18090525a5f1 (hf : ∀ i, MemLp (f i) 2 P)
    (C : ℝ≥0) (hb : ∀ i, ∫ ω, (f i ω) ^ 2 ∂P ≤ C) : UniformIntegrable f 1 P := by
  have hΦ : MeasureTheory.SuperlinearEnvelope (fun r : ℝ≥0 ↦ r ^ 2) := by
    have heq : (fun r : ℝ≥0 ↦ r ^ 2 / r) = id := by
      funext r
      by_cases hr : r = 0 <;> simp [pow_two, hr]
    rw [MeasureTheory.SuperlinearEnvelope, heq]
    exact tendsto_id
  apply _root_.Prove2MeSourceProof.h_a4946c6794948bd9996bb99a hΦ (measurable_id.pow_const 2)
    (fun i ↦ (hf i).aestronglyMeasurable) C
  intro i
  have heq : (fun ω ↦ ((‖f i ω‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)) =
      fun ω ↦ ENNReal.ofReal ((f i ω) ^ 2) := by
    funext ω
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp only [NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs]
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal (hf i).integrable_sq
    (ae_of_all P (fun ω ↦ sq_nonneg (f i ω)))]
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hb i)
end MeasureTheory


