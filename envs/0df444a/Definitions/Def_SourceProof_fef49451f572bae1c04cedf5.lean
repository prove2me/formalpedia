-- Prove2me | Definitions.Def_SourceProof_fef49451f572bae1c04cedf5
-- name    : SourceProof_fef49451f572bae1c04cedf5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:47.844436+00:00
-- url     : https://prove2.me/theorems/ace8a617-1f51-51d9-a857-6cbe56815a7e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsClassD.integrable_finiteStoppingTime_value

import Definitions.Def_StochLean_Probability_Process_ClassD_Basic_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Class D: uniform integrability of finite stopping values

The sole Class D predicate concerns the family of all everywhere-finite stopping
times, using the existing `FiniteStoppingTime` witness. Adaptation, cadlag paths,
one-sided martingality and initial normalization are separate hypotheses.
In particular this is not uniform integrability at deterministic times.
Source: Protter III.3, printed p.107 (PDF p.118).
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
  {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → E}

namespace IsClassD

theorem _root_.Prove2MeSourceProof.h_fef49451f572bae1c04cedf5 (hX : IsClassD X F P)
    (τ : FiniteStoppingTime F) : Integrable (fun ω ↦ X (τ ω) ω) P :=
  memLp_one_iff_integrable.mp (hX.memLp τ)
end IsClassD

end ProbabilityTheory


