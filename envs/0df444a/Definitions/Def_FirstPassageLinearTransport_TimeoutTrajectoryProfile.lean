-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
-- name    : FirstPassageLinearTransport_TimeoutTrajectoryProfile
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:26:26.908119+00:00
-- url     : https://prove2.me/theorems/8c301586-9935-5bd8-bd90-7dea7ff9919d
-- title:
--   Timeout Trajectory Profile
-- statement:
--   Definitions and structural lemmas for Timeout Trajectory Profile, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def shortcutLogDeviation (n j : ℕ) : ℝ :=
  Real.log (orbit j n) - Real.log n +
    driftGap * (j : ℝ) * Real.log 2
def rawLogDeviation (n i : ℕ) : ℝ :=
  Real.log (rawOrbit i n) - Real.log n +
    (2 * driftGap / 3) * (i : ℝ) * Real.log 2
def rawOddDeviationCoefficient : ℝ :=
  (2 * driftGap / 3) * Real.log 2
def timeoutRawTrajectorySupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  timeoutTimeSupportConstant P C +
    rawOddDeviationCoefficient *
      ((timeoutTimeSupportConstant P C + 1) / Real.log 3) + 1
noncomputable def shortcutFirstPassageTime (n : ℕ) (z : ℝ) : ℕ :=
  sInf {j : ℕ | (orbit j n : ℝ) ≤ z}
noncomputable def rawFirstPassageTime (n : ℕ) (z : ℝ) : ℕ :=
  sInf {i : ℕ | (rawOrbit i n : ℝ) ≤ z}
def timeoutOddTrajectorySupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  (timeoutTimeSupportConstant P C + 1) / Real.log 3
def timeoutCompletedOddTrajectorySupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  timeoutOddTrajectorySupportConstant P C +
    timeoutTimeSupportConstant P C
def timeoutCompletedRawTrajectorySupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  2 * timeoutTimeSupportConstant P C +
    rawOddDeviationCoefficient *
      timeoutCompletedOddTrajectorySupportConstant P C + 1
end
end FirstPassageLinearTransport


