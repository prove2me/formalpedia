-- Prove2me | Definitions.Def_SourceProof_cad965745163d481badd0dcb
-- name    : SourceProof_cad965745163d481badd0dcb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:14.426544+00:00
-- url     : https://prove2.me/theorems/eb43d518-15b4-4e18-8017-2b98ab3ff0e3
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.initialIncrement

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_6e9bb4c834a1b44d569cca8b
import Definitions.Def_SourceProof_ff07642989734d14cb2ac8eb
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Subtracting each path's initial value preserves UCP convergence -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {Z : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_cad965745163d481badd0dcb (hu : TendstoUCP P Z l Y) :
    TendstoUCP P (fun n t ω ↦ Z n t ω - Z n 0 ω) l
      (fun t ω ↦ Y t ω - Y 0 ω) := by
  have hs := (_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb hu) ((_root_.Prove2MeSourceProof.h_6e9bb4c834a1b44d569cca8b hu) (fun _ ↦ ⊥))
  simp only [stoppedProcess_const_bot] at hs
  exact hs
end TendstoUCP

end ProbabilityTheory


