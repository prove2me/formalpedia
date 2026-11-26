-- Prove2me | Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
-- name    : FirstPassageLinearTransport_MovingLowParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:14:28.726519+00:00
-- url     : https://prove2.me/theorems/be57bc98-4421-5496-84b7-32a911849f1e
-- title:
--   Moving Low Parameters
-- statement:
--   Definitions and structural lemmas for Moving Low Parameters, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingLowParameters.lean

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def movingLowTolerance (K₀ : ℝ) (L : ℕ) : ℝ :=
  driftGap - K₀ / (L : ℝ)
def movingLowRatio (K₀ : ℝ) (L : ℕ) : ℝ :=
  1 - K₀ / (2 * (L : ℝ))
def movingLowLambda (K₁ : ℝ) (L : ℕ) : ℝ :=
  1 - K₁ / (L : ℝ)
end
end FirstPassageLinearTransport


