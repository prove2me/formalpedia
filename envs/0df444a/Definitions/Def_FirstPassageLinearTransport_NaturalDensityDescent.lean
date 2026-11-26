-- Prove2me | Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
-- name    : FirstPassageLinearTransport_NaturalDensityDescent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:16:52.641034+00:00
-- url     : https://prove2.me/theorems/fbb887c7-d5ae-5a5b-a320-6425618be9bf
-- title:
--   Natural Density Descent
-- statement:
--   Definitions and structural lemmas for Natural Density Descent, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NaturalDensityDescent.lean

import Definitions.Def_FirstPassageLinearTransport_ClockBudget
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
end
end FirstPassageLinearTransport


