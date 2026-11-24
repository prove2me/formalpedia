-- Prove2me | Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
-- name    : SourceProof_2cbb2ed1687ae3057f41e0d2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:59:36.074844+00:00
-- url     : https://prove2.me/theorems/b4d66826-77e3-4202-b9a6-53e05e581489
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.adapted

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Semimartingales as good integrators

The canonical predicate is zero-sequential continuity of the elementary
integral for uniform convergence in `(t,ω)`. The epsilon/delta source
continuity criterion is proved equivalent. Classical decompositions are not
part of this definition. This file does not select a stochastic integral for
general caglad integrands or a quadratic variation.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

namespace IsSemimartingale

theorem _root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 (hX : IsSemimartingale X F P) : Adapted F X := by
  intro t
  have ht := (hX t).1 t
  have heq : stoppedProcess X (fun _ ↦ (t : WithTop ℝ≥0)) t = X t :=
    funext fun _ ↦ stoppedProcess_eq_of_le le_rfl
  rwa [heq] at ht
end IsSemimartingale

end ProbabilityTheory


