-- Prove2me | Definitions.Def_BrownSharedSignals_Fluid_ControlledProcess
-- name    : BrownSharedSignals_Fluid_ControlledProcess
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:45:34.078988+00:00
-- url     : https://prove2.me/theorems/8575522c-26af-44f0-ba5f-d30419d3197c
-- title:
--   Finite controlled Markov processes with an observed context
-- statement:
--   A finite controlled Markov process has a finite state carrier S and an observed context carrier Z. At each time t, state s and context z, the admissible actions form an arbitrary finite subset of the nonnegative real numbers containing zero. Each action has a real reward and a normalized probability distribution for the next local state. Time, state and context may change every part of this data. The definition is independent of resource sharing, projects and fluid control; it supplies the general controlled-process object used by the paper-specific model. It reuses the published finite probability distribution type.
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), §2, printed 5–6 / PDF 6–7

import Mathlib
import Definitions.Def_CountingMatroidSupport_Probability_FinDist

open scoped BigOperators
noncomputable section

namespace BrownSharedSignals.Fluid

/-- A finite nonstationary controlled Markov process with an observed external context.
The admissible real actions vary with time, state, and context; rewards are signed. -/
structure ControlledProcess (S Z : Type) [Fintype S] where
  actions : ℕ → S → Z → Finset ℝ
  zero_mem : ∀ t s z, 0 ∈ actions t s z
  action_nonneg : ∀ t s z a, a ∈ actions t s z → 0 ≤ a
  reward : ℕ → S → Z → ℝ → ℝ
  transition : ℕ → S → Z → ℝ → Arlib.Probability.FinDist S

end BrownSharedSignals.Fluid


