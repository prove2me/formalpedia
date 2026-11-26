-- Prove2me | Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
-- name    : FirstPassageLinearTransport_AdjustableBarrierDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:01:58.3208+00:00
-- url     : https://prove2.me/theorems/91278249-b4b1-59a6-8d70-4b4252d2fa5a
-- title:
--   Adjustable Barrier Density
-- statement:
--   Definitions and structural lemmas for Adjustable Barrier Density, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def adjustableBarrierDisplacement (lambda t : ℝ) : ℝ :=
  lambda * t / logTwoThree
end
end FirstPassageLinearTransport


