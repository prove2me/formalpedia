-- Prove2me | Definitions.Def_FirstPassageLinearTransport_StretchedLogLanding
-- name    : FirstPassageLinearTransport_StretchedLogLanding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:15:39.743744+00:00
-- url     : https://prove2.me/theorems/858ea79e-0df7-5290-a51c-752733f0cacf
-- title:
--   Stretched Log Landing
-- statement:
--   Definitions and structural lemmas for Stretched Log Landing, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedLogLanding.lean

import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
def descentAlpha (omega r : ℝ) : ℝ :=
  omega * Real.log (1 / r)
end
end FirstPassageLinearTransport


