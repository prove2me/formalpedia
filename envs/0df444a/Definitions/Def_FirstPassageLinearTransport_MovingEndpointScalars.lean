-- Prove2me | Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
-- name    : FirstPassageLinearTransport_MovingEndpointScalars
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:15:31.745105+00:00
-- url     : https://prove2.me/theorems/34826c28-0332-579b-80fb-ee464479ad4a
-- title:
--   Moving Endpoint Scalars
-- statement:
--   Definitions and structural lemmas for Moving Endpoint Scalars, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def firstPassageEntropyGap : ℝ :=
  1 - binaryEntropyBaseTwo logThreeTwo
def movingTerminalRank (A : ℕ → ℝ) (M : ℕ) : ℕ :=
  ⌈A M * Real.logb 2 ((M : ℝ) + 2)⌉₊
def criticalRankBuffer (L : ℕ → ℕ) (M : ℕ) : ℝ :=
  firstPassageEntropyGap * L M -
    (1 / 2) * Real.logb 2 ((M : ℝ) + 2) -
    Real.logb 2 (Real.log ((M : ℝ) + 3))
def movingRankBuffer (A : ℕ → ℝ) (M : ℕ) : ℝ :=
  criticalRankBuffer (movingTerminalRank A) M
def sharpMovingRankBuffer (A : ℕ → ℝ) (M : ℕ) : ℝ :=
  firstPassageEntropyGap * movingTerminalRank A M -
    (1 / 2) * Real.logb 2 ((M : ℝ) + 2)
end
end FirstPassageLinearTransport


