-- Prove2me | Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
-- name    : FirstPassageLinearTransport_MovingEndpointAsymptotics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:16:37.817613+00:00
-- url     : https://prove2.me/theorems/c1e4a483-f87c-4146-a154-6b44060480dc
-- title:
--   Moving Endpoint Asymptotics
-- statement:
--   Definitions and structural lemmas for Moving Endpoint Asymptotics, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointAsymptotics.lean

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeSupportScalars
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def movingEndpointProfileConstant
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta) (C D : ℝ) : ℝ :=
  let K := 1 + quadraticWindowShellConstant
  let T := movingTimeSupportConstant P.run P.Cswitch + 1
  let R := 1 + 6 / (P.run.rStar : ℝ)
  let Q := exactSharpCriticalLowSeriesConstant
    (firstPassageEndpointRate / 2) (C / 2)
  let B := Real.sqrt (Amax / Real.log 2 + 1) *
    Real.exp (firstPassageEndpointRate + D)
  K + T * R * K + 2 * T * R * Q * B
end
end FirstPassageLinearTransport


