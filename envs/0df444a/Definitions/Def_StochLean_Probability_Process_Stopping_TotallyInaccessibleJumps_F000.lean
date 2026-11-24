-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_TotallyInaccessibleJumps_F000
-- name    : StochLean_Probability_Process_Stopping_TotallyInaccessibleJumps_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:41.623943+00:00
-- url     : https://prove2.me/theorems/7b6fe3d5-8a41-4326-a80b-ef267c97dbc9
-- title:
--   StochLean: Probability.Process.Stopping.TotallyInaccessibleJumps F000

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Classification_F000
import Definitions.Def_SourceProof_264d677d5da3fcd447059c80

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Processes whose positive-time jumps are totally inaccessible

The source hypothesis is countable coverage of the nonzero positive-time jump graph by actual
totally inaccessible stopping times. It does not include adaptedness or path regularity, and it
does not constrain the initial value: the source convention makes `jumpProcess X 0 = X 0`.
Coverage implies zero jumps at predictable stopping times and total inaccessibility of any
stopping time carried by the nonzero positive-time jump graph. All statements use finite graph
points directly; no evaluation at an artificial finite replacement for infinity is needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Countably many totally inaccessible stopping times cover every nonzero positive-time jump
on one common full-measure event. Initial values, adaptedness and path regularity are separate
hypotheses rather than part of this jump-coverage predicate. -/
def HasTotallyInaccessibleJumps (F : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) : Prop :=
  ∃ σ : ℕ → Ω → WithTop ℝ≥0,
    (∀ n, IsTotallyInaccessibleStoppingTime F (σ n) P) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → jumpProcess X t ω ≠ 0 →
        ∃ n : ℕ, σ n ω = (t : WithTop ℝ≥0)
variable {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

end ProbabilityTheory


