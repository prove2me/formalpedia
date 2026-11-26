-- Prove2me | Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
-- name    : FirstPassageLinearTransport_ShrinkingTailAsymptotics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:15:48.498521+00:00
-- url     : https://prove2.me/theorems/da9a7b74-409f-4728-bef1-dd0f0b68594c
-- title:
--   Shrinking Tail Asymptotics
-- statement:
--   Definitions and structural lemmas for Shrinking Tail Asymptotics, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTailAsymptotics.lean

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def shrinkingHighDensityProfile
    (P : ShrinkingBarrierRunData) (C : ℝ) (M : ℕ) : ℝ :=
  Real.exp (-(Real.log 2 * (shrinkingSwitchRank C M : ℝ))) +
    quadraticWindowShellConstant *
      Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
        Real.log ((M : ℝ) + 2)))
def shrinkingPolylogProfileConstant
    (P : ShrinkingBarrierRunData) (C b b' c' : ℝ) : ℝ :=
  let K := 1 + quadraticWindowShellConstant
  let T := shrinkingTimeSupportConstant P C + 1
  let R := 1 + 6 / (P.rStar : ℝ)
  K + T * R * (K + terminalTailPrefactor b b' c')
end
end FirstPassageLinearTransport


