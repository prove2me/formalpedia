-- Prove2me | Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
-- name    : FirstPassageLinearTransport_EntropyBarrier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:00:26.079816+00:00
-- url     : https://prove2.me/theorems/db7d7933-f40b-518e-9398-95426d7f3bdd
-- title:
--   Entropy Barrier
-- statement:
--   Definitions and structural lemmas for Entropy Barrier, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
def booleanLegendreRate (t θ : ℝ) : ℝ :=
  2 * t * θ - Real.log (Real.cosh θ)
def binaryBarrierRate (t : ℝ) : ℝ :=
  Real.log 2 - Real.binEntropy (1 / 2 + t)
def booleanOptimizer (t : ℝ) : ℝ :=
  (Real.log (1 / 2 + t) - Real.log (1 / 2 - t)) / 2
end
end FirstPassageLinearTransport


