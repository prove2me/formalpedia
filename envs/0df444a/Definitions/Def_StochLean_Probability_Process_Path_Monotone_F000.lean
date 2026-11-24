-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_Monotone_F000
-- name    : StochLean_Probability_Process_Path_Monotone_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:26.265749+00:00
-- url     : https://prove2.me/theorems/be03e7c9-5fdb-4ed4-9ea8-04251ae687c1
-- title:
--   StochLean: Probability.Process.Path.Monotone F000

import Definitions.Def_StochLean_Probability_Process_Equivalence_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Almost-sure monotone paths

Path properties are stated on one common full-measure event. This is stronger than having an
exceptional null set that may depend on a pair of times.
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}

/-- A process has almost-sure monotone paths when one common full-measure event supports a
monotone trajectory at every time. -/
def HasMonotonePaths [Preorder T] [Preorder E] (X : T → Ω → E)
    (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, Monotone fun t ↦ X t ω
namespace HasMonotonePaths

variable [Preorder T] [Preorder E] {X Y : T → Ω → E} {P : Measure Ω}

end HasMonotonePaths

end ProbabilityTheory


