-- Prove2me | Definitions.Def_SourceProof_1079144fe60f0ff536db6816
-- name    : SourceProof_1079144fe60f0ff536db6816
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:45:34.567506+00:00
-- url     : https://prove2.me/theorems/7eb47d8a-0803-4815-915d-8728d419f897
-- title:
--   StochLean source theorem: StochLean.isCadlagPath_tprod_Ioc

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_654d2425a87bc54fc263e3bf
import Definitions.Def_SourceProof_72088dc48dc4fadc17241483
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # One-sided regularity of locally absolutely convergent cumulative products

Closed positive-time products include the jump at the current time; their
strict-left limits are the products on the corresponding open interval.
Zero and negative factors are permitted. Dominated convergence is applied
to deviations from one, not to logarithms of possibly nonpositive factors.
-/

@[expose] public section

open Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_1079144fe60f0ff536db6816 {f : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |f s - 1|)) :
    IsCadlagPath (fun t : ℝ≥0 ↦ ∏' s : Ioc 0 t, f s) :=
  ⟨_root_.Prove2MeSourceProof.h_654d2425a87bc54fc263e3bf hs, fun t _ ↦ ⟨_, _root_.Prove2MeSourceProof.h_72088dc48dc4fadc17241483 hs t⟩⟩
end StochLean


