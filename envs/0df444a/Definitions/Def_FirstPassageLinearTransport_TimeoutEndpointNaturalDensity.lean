-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
-- name    : FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:29:02.853072+00:00
-- url     : https://prove2.me/theorems/56254d94-7edf-58bc-983f-ce52f6c7ae15
-- title:
--   Timeout Endpoint Natural Density
-- statement:
--   Definitions and structural lemmas for Timeout Endpoint Natural Density, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointNaturalDensity.lean

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAssembly
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointWitness
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def timeoutEndpointWitnessGood
    (A : ℕ → ℝ) (c beta C : ℝ) (M : ℕ) : Set ℕ :=
  {n : ℕ | ∃ k : ℕ,
    (k : ℝ) < c * Real.log n ∧
    (orbit k n : ℝ) < C * (Real.log n) ^ (A M) ∧
    ∀ j : ℕ, j ≤ k →
      (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)}
end
end FirstPassageLinearTransport


