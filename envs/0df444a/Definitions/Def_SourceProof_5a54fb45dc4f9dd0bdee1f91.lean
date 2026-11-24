-- Prove2me | Definitions.Def_SourceProof_5a54fb45dc4f9dd0bdee1f91
-- name    : SourceProof_5a54fb45dc4f9dd0bdee1f91
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:31.277043+00:00
-- url     : https://prove2.me/theorems/9aa55fed-b429-4259-ba4a-13ca4e14d95d
-- title:
--   StochLean source theorem: ProbabilityTheory.isCagladPath_step_Ioc

import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_2788bc818189572242b6cda6
import Definitions.Def_SourceProof_666dd1ca96d37833a039b8b0
import Definitions.Def_SourceProof_669e70af113890cd7317fc66
import Definitions.Def_SourceProof_7cdb042af88bfa80a4278508
import Definitions.Def_SourceProof_7fe27d80761f531095784a17
import Definitions.Def_SourceProof_f27f0406d0856e73dc290674
import Mathlib.Analysis.Normed.Group.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Caglad initial spikes and left-open, right-closed step paths -/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_5a54fb45dc4f9dd0bdee1f91 {a b : ℝ≥0} (hab : a ≤ b) (c : ℝ) :
    IsCagladPath (fun t : ℝ≥0 ↦ if a < t ∧ t ≤ b then c else 0) := by
  have h := (_root_.Prove2MeSourceProof.h_2788bc818189572242b6cda6 (_root_.Prove2MeSourceProof.h_7cdb042af88bfa80a4278508 a c))
    ((_root_.Prove2MeSourceProof.h_666dd1ca96d37833a039b8b0 (_root_.Prove2MeSourceProof.h_7cdb042af88bfa80a4278508 b c)) continuous_neg)
  convert h using 1
  funext t
  by_cases ha : a < t <;> by_cases hb : b < t
  · simp [ha, hb, not_le_of_gt hb]
  · simp [ha, hb, le_of_not_gt hb]
  · exact (ha (hab.trans_lt hb)).elim
  · simp [ha, hb]
end ProbabilityTheory


