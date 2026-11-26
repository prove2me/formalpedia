-- Prove2me | Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
-- name    : FirstPassageLinearTransport_PolylogTerminalSchedule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:55:33.389785+00:00
-- url     : https://prove2.me/theorems/7ddce2e6-6079-5c44-af7e-93ec60c78eb5
-- title:
--   Polylog Terminal Schedule
-- statement:
--   Definitions and structural lemmas for Polylog Terminal Schedule, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogTerminalSchedule.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def polylogTerminalRank (A : ℝ) (M : ℕ) : ℕ :=
  ⌈A * Real.logb 2 ((M : ℝ) + 2)⌉₊
end
end FirstPassageLinearTransport


