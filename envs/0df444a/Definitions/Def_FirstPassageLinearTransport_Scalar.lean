-- Prove2me | Definitions.Def_FirstPassageLinearTransport_Scalar
-- name    : FirstPassageLinearTransport_Scalar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:12:49.546811+00:00
-- url     : https://prove2.me/theorems/a9aa7e8b-4977-410a-8884-512773d3c946
-- title:
--   Scalar
-- statement:
--   Definitions and structural lemmas for Scalar, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Scalar.lean

import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter Asymptotics
noncomputable section
def stageCount (omega : ℝ) (M : ℕ) : ℕ :=
  ⌊omega * Real.log (M + 4)⌋₊
end
end FirstPassageLinearTransport


