-- Prove2me | Definitions.Def_SourceProof_ba0c3283c5dd23de3dd55b0c
-- name    : SourceProof_ba0c3283c5dd23de3dd55b0c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:00:40.488235+00:00
-- url     : https://prove2.me/theorems/828d46db-1f19-4271-84bb-e7148923a542
-- title:
--   StochLean source theorem: ProbabilityTheory.HasLaw.integrable_natCast_poissonMeasure

import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Definitions.Def_SourceProof_db86699b96bdd02e6e9ffb79
import Mathlib.Analysis.Calculus.Deriv.Slope

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Interval-count axioms for Poisson processes

This file formalizes Klenke's interval axioms P1--P5 for a counting process.  In addition to
those axioms, the predicate records the design-level path convention used by StochLean: paths are
almost surely monotone and right-continuous on one common event, and the process starts at zero.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace HasLaw

theorem _root_.Prove2MeSourceProof.h_ba0c3283c5dd23de3dd55b0c {P : Measure Ω} {Y : Ω → ℕ} {r : NNReal}
    (hY : HasLaw Y (poissonMeasure r) P) : Integrable (fun ω ↦ (Y ω : ℝ)) P := by
  have hmap : Integrable (fun n : ℕ ↦ (n : ℝ)) (P.map Y) := by
    rw [hY.map_eq]
    exact _root_.Prove2MeSourceProof.h_db86699b96bdd02e6e9ffb79 r
  simpa only [Function.comp_def] using hmap.comp_aemeasurable hY.aemeasurable
end HasLaw

namespace IsPoissonProcess

variable {X : NNReal → Ω → ℕ} {rate : NNReal} {P : Measure Ω} [IsProbabilityMeasure P]

end IsPoissonProcess

end ProbabilityTheory


