-- Prove2me | Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
-- name    : FirstPassageLinearTransport_FixedPolylogParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:13:49.068397+00:00
-- url     : https://prove2.me/theorems/39e25396-e398-4eb9-8a1e-012dcb581c9f
-- title:
--   Fixed Polylog Parameters
-- statement:
--   Definitions and structural lemmas for Fixed Polylog Parameters, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedPolylogParameters.lean

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def firstPassageEndpointDisplacement : ℝ := driftGap / logTwoThree
def firstPassageEndpointRate : ℝ :=
  binaryBarrierRate firstPassageEndpointDisplacement
def fixedPolylogCriticalExponent : ℝ :=
  Real.log 2 / firstPassageEndpointRate
def logThreeTwo : ℝ := Real.log 2 / Real.log 3
def binaryEntropyBaseTwo (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2
def endpointLambda (n : ℕ) : ℝ :=
  1 - 1 / ((n : ℝ) + 2)
def endpointTolerance (n : ℕ) : ℝ :=
  driftGap * endpointLambda n
def fixedPolylogClockCritical : ℝ :=
  1 / (driftGap * Real.log 2)
end
end FirstPassageLinearTransport


