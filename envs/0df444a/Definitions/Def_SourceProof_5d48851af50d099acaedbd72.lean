-- Prove2me | Definitions.Def_SourceProof_5d48851af50d099acaedbd72
-- name    : SourceProof_5d48851af50d099acaedbd72
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:47:52.965136+00:00
-- url     : https://prove2.me/theorems/40b229a1-ee32-4fc0-a57f-5a03a0dde3bb
-- title:
--   StochLean source theorem: MeasureTheory.isUIMartingale_tsum_indicator_sub_condExp_before

import Definitions.Def_SourceProof_d15413cea1756ce85082d92a
import Definitions.Def_SourceProof_f1c30f585c827714ee7a1fac

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual sums of centered integrable lifetime jumps

Summable coefficient first moments provide an actual integrable envelope on
one common event of absolute convergence. Finite partial sums are martingales;
their coordinatewise UI convergence proves martingality of the original tsum.
The same envelope gives UI over the entire time axis.

The source centering theorem uses the actual conditional expectation before
each stopping lifetime. No predictability, finite lifetime, initial-value
normalization, candidate terminal or assumed series convergence is needed.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : ℕ → Ω → WithTop ℝ≥0} {C Z : ℕ → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_5d48851af50d099acaedbd72
    (hτ : ∀ n, IsStoppingTime F (τ n))
    (hm : ∀ n, StronglyMeasurable[(hτ n).measurableSpace] (Z n))
    (hi : ∀ n, Integrable (Z n) P)
    (hs : Summable (fun n ↦ ∫ ω, ‖Z n ω‖ ∂P)) :
    IsUIMartingale (fun t ω ↦ ∑' n,
      {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator
        (Z n - P[Z n | (hτ n).measurableSpaceBefore]) ω) F P := by
  let C : ℕ → Ω → ℝ := fun n ↦ Z n - P[Z n | (hτ n).measurableSpaceBefore]
  have hiC (n : ℕ) : Integrable (C n) P := (hi n).sub integrable_condExp
  have hbound (n : ℕ) : (∫ ω, ‖C n ω‖ ∂P) ≤
      (∫ ω, ‖Z n ω‖ ∂P) + (∫ ω, ‖Z n ω‖ ∂P) := by
    calc
      _ ≤ ∫ ω, ‖Z n ω‖ + ‖P[Z n | (hτ n).measurableSpaceBefore] ω‖ ∂P :=
        integral_mono (hiC n).norm ((hi n).norm.add integrable_condExp.norm)
          (fun ω ↦ norm_sub_le _ _)
      _ = (∫ ω, ‖Z n ω‖ ∂P) +
          ∫ ω, ‖P[Z n | (hτ n).measurableSpaceBefore] ω‖ ∂P :=
        integral_add (hi n).norm integrable_condExp.norm
      _ ≤ _ := add_le_add le_rfl (integral_norm_condExp_le (Z n))
  have hsC : Summable (fun n ↦ ∫ ω, ‖C n ω‖ ∂P) :=
    (hs.add hs).of_nonneg_of_le (fun n ↦ integral_nonneg fun ω ↦ norm_nonneg (C n ω))
      hbound
  exact _root_.Prove2MeSourceProof.h_d15413cea1756ce85082d92a
    (fun n ↦ _root_.Prove2MeSourceProof.h_f1c30f585c827714ee7a1fac (hτ n) (hm n) (hi n)) hiC hsC
end MeasureTheory


