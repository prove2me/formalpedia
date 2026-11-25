-- Prove2me | Definitions.Def_SourceProof_f90bd334d926b7a0f3f6f377
-- name    : SourceProof_f90bd334d926b7a0f3f6f377
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:17:17.01344+00:00
-- url     : https://prove2.me/theorems/cf6aa20c-ded8-4abd-a9dc-ce54f43361a8
-- title:
--   StochLean source theorem: ProbabilityTheory.isCagladPath_initialSpike

import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_2788bc818189572242b6cda6
import Definitions.Def_SourceProof_50bef199e170152e0882c89e
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

theorem _root_.Prove2MeSourceProof.h_f90bd334d926b7a0f3f6f377 (c : ℝ) :
    IsCagladPath (fun t : ℝ≥0 ↦ if t = 0 then c else 0) := by
  have hconst : ProbabilityTheory.IsCagladPath (fun _ : ℝ≥0 ↦ c) :=
    _root_.Prove2MeSourceProof.h_50bef199e170152e0882c89e continuous_const
  have h := (_root_.Prove2MeSourceProof.h_2788bc818189572242b6cda6 hconst) ((_root_.Prove2MeSourceProof.h_666dd1ca96d37833a039b8b0 (_root_.Prove2MeSourceProof.h_7cdb042af88bfa80a4278508 0 c)) continuous_neg)
  convert h using 1
  funext t
  by_cases ht : t = 0
  · simp [ht]
  · simp [ht, pos_iff_ne_zero.mpr ht]
end ProbabilityTheory


