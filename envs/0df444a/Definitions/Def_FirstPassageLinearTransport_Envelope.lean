-- Prove2me | Definitions.Def_FirstPassageLinearTransport_Envelope
-- name    : FirstPassageLinearTransport_Envelope
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:00:11.147872+00:00
-- url     : https://prove2.me/theorems/6c8b243a-8ae0-4793-ba14-ea24d65efa1e
-- title:
--   Envelope
-- statement:
--   Definitions and structural lemmas for Envelope, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
def logTwoThree : ℝ := Real.log 3 / Real.log 2
def a0 : ℝ := logTwoThree / 2
def rho : ℝ := Real.sqrt 3 / 2
def centralOrbitScale (k : ℕ) : ℝ :=
  (3 : ℝ) ^ ((k : ℝ) / 2) / (2 : ℝ) ^ k
def parityDigitR (n i : ℕ) : ℝ := (parityBit n i : ℕ)
def normalizedCorrectionTerm (k n i : ℕ) : ℝ :=
  parityDigitR n i /
    ((3 : ℝ) ^ oddCount n (i + 1) * (2 : ℝ) ^ (k - i))
def normalizedCorrection (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, normalizedCorrectionTerm k n i
def driftGap : ℝ := 1 - a0
def maximalBarrierHeight (t : ℝ) (M : ℕ) : ℝ :=
  t * M / (2 * logTwoThree)
end
end FirstPassageLinearTransport


