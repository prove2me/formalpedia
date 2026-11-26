-- Prove2me | Definitions.Def_FirstPassageLinearTransport_BarrierDensity
-- name    : FirstPassageLinearTransport_BarrierDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:01:26.729123+00:00
-- url     : https://prove2.me/theorems/f930144a-c2b7-42b4-9801-aa6f27f5429e
-- title:
--   Barrier Density
-- statement:
--   Definitions and structural lemmas for Barrier Density, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
def initialWindowGood (t : ℝ) : Set ℕ :=
  {n | ∀ k : ℕ, k ≤ Nat.log 2 n →
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) ∧
      (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t)}
noncomputable def shellInitialWindowBad (M : ℕ) (t : ℝ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter (fun n =>
    ∃ k : ℕ, k ≤ M ∧
      ((orbit k n : ℝ) < centralOrbitScale k * (n : ℝ) ^ (1 - t) ∨
        centralOrbitScale k * (n : ℝ) ^ (1 + t) < (orbit k n : ℝ)))
def maximalBarrierC0 : ℝ := 1 / (2 * logTwoThree ^ 2)
def quadraticWindowShellConstant : ℝ :=
  2 * Real.exp (4 * maximalBarrierC0)
def quadraticWindowDensityRate (t : ℝ) : ℝ :=
  maximalBarrierC0 * t ^ 2 / Real.log 2
def quadraticWindowGlobalConstant (t : ℝ) : ℝ :=
  2 * quadraticWindowShellConstant /
    (2 * Real.exp (-(maximalBarrierC0 * t ^ 2)) - 1)
end
end FirstPassageLinearTransport


