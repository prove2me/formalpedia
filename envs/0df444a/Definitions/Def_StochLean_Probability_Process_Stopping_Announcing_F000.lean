-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Announcing_F000
-- name    : StochLean_Probability_Process_Stopping_Announcing_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:24.425246+00:00
-- url     : https://prove2.me/theorems/a548313e-1d62-41e1-a87a-170aa4cdd6b8
-- title:
--   StochLean: Probability.Process.Stopping.Announcing F000

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_BeforeSigmaOrder_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Announcing sequences and predictable stopping times

The source Protter III.2 convention allows zero and infinite lifetimes. An
announcing sequence is pointwise increasing, strictly below the lifetime on
its positive event, and converges almost surely. In particular, almost-sure
convergence is not silently replaced by everywhere convergence.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Witness relation from Protter III.2. It does not choose an announcing sequence. -/
structure IsAnnouncingSequence (F : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (τ : Ω → WithTop ℝ≥0) (σ : ℕ → Ω → WithTop ℝ≥0) : Prop where
  isStoppingTime : ∀ n, IsStoppingTime F (σ n)
  monotone : ∀ ω, Monotone (fun n ↦ σ n ω)
  strict : ∀ n ω, 0 < τ ω → σ n ω < τ ω
  tendsto : ∀ᵐ ω ∂P, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω))
/-- Predictability of a stopping time is existence of source announcing data,
not an identification with accessibility or predictability of an arbitrary graph. -/
def IsPredictableStoppingTime (F : Filtration ℝ≥0 mΩ) (τ : Ω → WithTop ℝ≥0)
    (P : Measure Ω) : Prop :=
  IsStoppingTime F τ ∧ ∃ σ, IsAnnouncingSequence F P τ σ
namespace IsAnnouncingSequence

variable {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {τ : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → WithTop ℝ≥0}

end IsAnnouncingSequence

end ProbabilityTheory


