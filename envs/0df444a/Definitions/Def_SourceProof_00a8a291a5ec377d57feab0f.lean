-- Prove2me | Definitions.Def_SourceProof_00a8a291a5ec377d57feab0f
-- name    : SourceProof_00a8a291a5ec377d57feab0f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:18:43.487081+00:00
-- url     : https://prove2.me/theorems/c74a4774-bc80-4ee7-924f-19cbca55dc95
-- title:
--   StochLean source theorem: ProbabilityTheory.HasFiniteVariationPaths.isSemimartingale

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_000ab664e2ae71af9a90c2da
import Definitions.Def_SourceProof_056f0ffa0965e1b3a522e2ff
import Definitions.Def_SourceProof_0c128e2930b7b6bb59b5789b
import Definitions.Def_SourceProof_5b103fdcc1107ebacb54c8cc
import Definitions.Def_SourceProof_723deac9757f6f9a48c688f4
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_faea1308e58b2b1b6deb90cf
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adapted cadlag finite-variation processes are semimartingales

Protter II.7 follows directly from the pathwise elementary-integral bound. The random
variation need not be integrable. This does not yet construct a Stieltjes measure or the
general Chapter II integral.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}

namespace HasFiniteVariationPaths
theorem _root_.Prove2MeSourceProof.h_00a8a291a5ec377d57feab0f (hf : HasFiniteVariationPaths X P)
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    IsSemimartingale X F P := by
  intro T
  change ProbabilityTheory.IsTotalSemimartingale (stoppedProcess X (ProbabilityTheory.FiniteStoppingTime.const F T).withTop) F P
  rw [_root_.Prove2MeSourceProof.h_faea1308e58b2b1b6deb90cf]
  have hstop : Adapted F (fun t ↦ X (min t T)) :=
    fun t ↦ (ha _).mono (F.mono (min_le_left t T)) le_rfl
  have hcad : ProbabilityTheory.HasCadlagPaths (fun t ↦ X (min t T)) P := hc.mono (fun _ h ↦ (_root_.Prove2MeSourceProof.h_056f0ffa0965e1b3a522e2ff h) T)
  refine ⟨hstop, hcad, ?_⟩
  apply _root_.Prove2MeSourceProof.h_5b103fdcc1107ebacb54c8cc
    (fun ω ↦ ‖X 0 ω‖ + (eVariationOn (fun t ↦ X t ω) (Icc 0 T)).toReal)
    (fun _ hH ↦
      ((_root_.Prove2MeSourceProof.h_723deac9757f6f9a48c688f4 hH) hstop hF (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hcad)).aestronglyMeasurable)
  filter_upwards [_root_.Prove2MeSourceProof.h_000ab664e2ae71af9a90c2da.mp hf] with ω hω
  refine ⟨by positivity, fun H hH C hC hb ↦ ?_⟩
  exact (_root_.Prove2MeSourceProof.h_0c128e2930b7b6bb59b5789b hH.choose) hC
    (by simpa only [hH.choose_spec] using hb) ω T (hω T)
end HasFiniteVariationPaths

end ProbabilityTheory


