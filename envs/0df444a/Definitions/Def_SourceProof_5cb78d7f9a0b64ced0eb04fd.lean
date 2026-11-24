-- Prove2me | Definitions.Def_SourceProof_5cb78d7f9a0b64ced0eb04fd
-- name    : SourceProof_5cb78d7f9a0b64ced0eb04fd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:46.805452+00:00
-- url     : https://prove2.me/theorems/706000ac-db08-4442-9346-904b1327ab8f
-- title:
--   StochLean source theorem: ProbabilityTheory.initialValueLocalizer_isFundamentalSequence

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_InitialValue_F000
import Definitions.Def_SourceProof_268eb95cb654b94024942d81
import Definitions.Def_SourceProof_619a18497398a378d9ad0e1b
import Definitions.Def_SourceProof_ae5a010f00e486e1966df2cd

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial-value safeguards for local martingales

Any finite F₀-measurable random variable defines a constant Protter local
martingale, even without integrability. Unmasked localization cannot remove
the initial value or make an unbounded initial value bounded.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {Z : Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_5cb78d7f9a0b64ced0eb04fd [IsFiniteMeasure P]
    [SigmaFiniteFiltration P F] (hZ : Measurable[F 0] Z) :
    IsFundamentalSequence (fun _ : ℝ≥0 ↦ Z) F P (initialValueLocalizer Z) := by
  refine ⟨⟨_root_.Prove2MeSourceProof.h_268eb95cb654b94024942d81 hZ,
    ae_of_all _ (_root_.Prove2MeSourceProof.h_ae5a010f00e486e1966df2cd Z)⟩,
    _root_.Prove2MeSourceProof.h_619a18497398a378d9ad0e1b Z, fun n ↦ ?_⟩
  let s : Set Ω := {ω | |Z ω| ≤ (n : ℝ)}
  have hs : MeasurableSet[F 0] s := by
    let : MeasurableSpace Ω := F 0
    simpa only [Real.norm_eq_abs] using measurableSet_le hZ.norm measurable_const
  have hb : ∀ ω, ‖s.indicator Z ω‖ ≤ (n : ℝ) := by
    intro ω
    by_cases h : ω ∈ s
    · simpa only [Set.indicator_of_mem h, Real.norm_eq_abs] using
        (show |Z ω| ≤ (n : ℝ) from h)
    · simp [Set.indicator_of_notMem h]
  have hm := hZ.stronglyMeasurable.indicator hs
  have hlp : MemLp (s.indicator Z) 1 P :=
    MemLp.of_bound (hm.mono (F.le 0)).aestronglyMeasurable n (ae_of_all _ hb)
  have hui : ProbabilityTheory.IsUIMartingale (fun _ : ℝ≥0 ↦ s.indicator Z) F P :=
    ⟨martingale_const_fun F P hm (memLp_one_iff_integrable.mp hlp),
      uniformIntegrable_const le_rfl (by simp) hlp⟩
  have heq : stoppedProcess
      (fun _ : ℝ≥0 ↦ {ω | 0 < ProbabilityTheory.initialValueLocalizer Z n ω}.indicator Z)
      (ProbabilityTheory.initialValueLocalizer Z n) = fun _ : ℝ≥0 ↦ s.indicator Z := by
    rw [stoppedProcess_const]
    funext t ω
    by_cases h : |Z ω| ≤ (n : ℝ) <;> simp [ProbabilityTheory.initialValueLocalizer, s, h]
  rwa [heq]
end ProbabilityTheory


