-- Prove2me | Definitions.Def_SourceProof_752c0bc3f1b08be0f7be8e77
-- name    : SourceProof_752c0bc3f1b08be0f7be8e77
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:22.548688+00:00
-- url     : https://prove2.me/theorems/d992837b-5b3c-4173-9167-01520a528ccf
-- title:
--   StochLean source theorem: ProbabilityTheory.norm_le_of_lt_cappedNormExitSequence

import Definitions.Def_SourceProof_1e52c15149bd45e1ab3198d1
import Definitions.Def_SourceProof_20658b06a283e28f60cf4a72

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Capped open norm exits for cadlag localization

The stopping sequence is the existing open norm hit, capped by its increasing
integer threshold. Cadlag compact bounds imply divergence. Strictly before
the exit, the path is bounded by the threshold, and the same bound holds for
its left limit at the exit. A bound on positive-time jumps controls overshoot.

Without a jump bound the stopped process is not claimed to be bounded. Only
its jumps away from the stopping endpoint are at most twice the threshold;
the non-strict inequality and the exceptional endpoint are retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem _root_.Prove2MeSourceProof.h_752c0bc3f1b08be0f7be8e77 {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) < cappedNormExitSequence X n ω) :
    ‖X t ω‖ ≤ ((n + 1 : ℕ) : ℝ) :=
  _root_.Prove2MeSourceProof.h_1e52c15149bd45e1ab3198d1
    (ht.trans_le (_root_.Prove2MeSourceProof.h_20658b06a283e28f60cf4a72 X n ω))
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


