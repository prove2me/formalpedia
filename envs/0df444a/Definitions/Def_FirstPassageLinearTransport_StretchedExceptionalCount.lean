-- Prove2me | Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
-- name    : FirstPassageLinearTransport_StretchedExceptionalCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:27:42.075733+00:00
-- url     : https://prove2.me/theorems/20b82bdc-ea67-4a40-80d2-59d556ae3cc8
-- title:
--   Stretched Exceptional Count
-- statement:
--   Definitions and structural lemmas for Stretched Exceptional Count, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedExceptionalCount.lean

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
set_option autoImplicit true
set_option maxHeartbeats 1000000
namespace FirstPassageLinearTransport
namespace QuantitativeDensity
open scoped Real Topology BigOperators
noncomputable section
def stretchedShellScale (M : ℕ) : ℝ :=
  (M : ℝ) + 4
def stretchedDyadicRate (c : ℝ) : ℝ :=
  min (c / 4) (Real.log 2 / 4)
end
end QuantitativeDensity
end FirstPassageLinearTransport


