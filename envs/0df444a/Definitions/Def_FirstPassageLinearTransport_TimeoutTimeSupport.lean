-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
-- name    : FirstPassageLinearTransport_TimeoutTimeSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:17:15.486096+00:00
-- url     : https://prove2.me/theorems/5a1ff8f1-ef0d-536b-ae59-6c0bfe6060c6
-- title:
--   Timeout Time Support
-- statement:
--   Definitions and structural lemmas for Timeout Time Support, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def timeoutDurationError (t : ℝ) (m : ℕ) : ℝ :=
  t * (m : ℝ) + t + 3
def timeoutTimePotential
    (P : TimeoutHighRunData) (M S q : ℕ) : ℝ :=
  if S < q then
    ((P.D + P.tau + 3) *
        Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt q) /
          (1 - Real.sqrt (P.rHi : ℝ)) + (S : ℝ) ^ 2
  else
    (S : ℝ) * (q : ℝ)
def timeoutFeasibleTimeCutoff
    (P : TimeoutHighRunData) (M S : ℕ) : ℕ :=
  ⌈((((M + 1 : ℕ) : ℝ) + timeoutTimePotential P M S (M + 1)) /
      driftGap)⌉₊
noncomputable def timeoutFeasibleTimes
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (L M S q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (timeoutFeasibleTimeCutoff P M S + 1)).filter fun h =>
    ∃ n : ℕ, n ∈ dyadicShell M ∧
      TimeoutRecertificationRun P K₀ L M S n h q
def timeoutTimeSupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  2 + 2 / driftGap *
    ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
      (C + 5) ^ 2)
end
end FirstPassageLinearTransport


