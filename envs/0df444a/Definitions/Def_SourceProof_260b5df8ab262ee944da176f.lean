-- Prove2me | Definitions.Def_SourceProof_260b5df8ab262ee944da176f
-- name    : SourceProof_260b5df8ab262ee944da176f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:17.635465+00:00
-- url     : https://prove2.me/theorems/2d1343e4-b2ed-4227-8571-22c01fe2d380
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.isUIMartingale_of_integrable_envelope

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_SourceProof_4d66c8d394bf81c5a531f8d4
import Definitions.Def_SourceProof_ee840a5a1d49268537816d0e
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Dominated local martingales are martingales

The proof takes limits in the defining set-integral identities of the masked
fundamental sequence. Thus it does not require continuous-time optional
sampling or a semimartingale decomposition.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0}

namespace IsLocalMartingale

theorem _root_.Prove2MeSourceProof.h_260b5df8ab262ee944da176f
    [SigmaFiniteFiltration P F] (hX : IsLocalMartingale X F P)
    {R : Ω → ℝ} (hR : Integrable R P)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ R ω) : IsUIMartingale X F P := by
  have hm := (_root_.Prove2MeSourceProof.h_ee840a5a1d49268537816d0e hX) fun _ ↦
    ⟨R, hR, hb.mono fun _ hω t _ ↦ hω t⟩
  refine ⟨hm, ?_⟩
  have hu : UniformIntegrable (fun _ : ℝ≥0 ↦ R) 1 P :=
    uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.mpr hR)
  apply (_root_.Prove2MeSourceProof.h_4d66c8d394bf81c5a531f8d4 hu) (fun t ↦ (hm.integrable t).aestronglyMeasurable)
  intro t
  filter_upwards [hb] with ω hω
  exact (hω t).trans (le_abs_self _)
end IsLocalMartingale

end ProbabilityTheory


