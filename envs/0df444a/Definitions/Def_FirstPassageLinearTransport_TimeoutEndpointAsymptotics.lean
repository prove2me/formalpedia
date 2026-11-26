-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
-- name    : FirstPassageLinearTransport_TimeoutEndpointAsymptotics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:23:00.694575+00:00
-- url     : https://prove2.me/theorems/1090df95-4511-464d-a855-2ac0012bd09e
-- title:
--   Timeout Endpoint Asymptotics
-- statement:
--   Definitions and structural lemmas for Timeout Endpoint Asymptotics, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointAsymptotics.lean

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def timeoutEndpointProfileConstant
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta) (C D : ℝ) : ℝ :=
  2 * movingEndpointProfileConstant P C D
def sharpTimeoutEndpointProfileConstant
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta) (D : ℝ) : ℝ :=
  let K := 1 + quadraticWindowShellConstant
  let T := timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1
  let G := 1 + 6 / (P.run.rStar : ℝ)
  let Q := 3 * (D / 2) * weightedTailConstant
    firstPassageEndpointRate (firstPassageEndpointRate / 2)
  let B := Real.sqrt (2 * firstPassageEndpointRate)
  K + T * G * K + T * G * Q * B
end
end FirstPassageLinearTransport


