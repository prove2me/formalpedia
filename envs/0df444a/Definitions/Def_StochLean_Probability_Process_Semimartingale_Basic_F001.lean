-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
-- name    : StochLean_Probability_Process_Semimartingale_Basic_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:00.842199+00:00
-- url     : https://prove2.me/theorems/5a37d653-c547-43a0-937e-36be081b0777
-- title:
--   StochLean: Probability.Process.Semimartingale.Basic F001

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F000

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

/-- Protter total semimartingale: adapted, cadlag, and a good integrator. -/
def IsTotalSemimartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  Adapted F X ∧ HasCadlagPaths X P ∧ IsGoodIntegrator X F P
/-- Protter ordinary semimartingale: every deterministic finite stopping is total. -/
def IsSemimartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  ∀ t : ℝ≥0, IsTotalSemimartingale (stoppedProcess X (fun _ ↦ (t : WithTop ℝ≥0))) F P
end ProbabilityTheory


