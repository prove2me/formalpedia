-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
-- name    : FirstPassageLinearTransport_TimeoutEnvelope
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:19:27.123811+00:00
-- url     : https://prove2.me/theorems/95b1ea8f-70be-5083-a1ea-bfaf5a392ec6
-- title:
--   Timeout Envelope
-- statement:
--   Definitions and structural lemmas for Timeout Envelope, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEnvelope.lean

import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
def timeoutHighTargetTolerance
    (P : TimeoutHighRunData) (M q : ℕ) : ℝ :=
  timeoutHighTolerance P M (q - 1)
noncomputable def timeoutHighFirstBadSourcesAtRank
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (L M S q : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n =>
    ∃ h : ℕ, TimeoutRecertificationRun P K₀ L M S n h q ∧
      orbit h n ∈ landingBad q (timeoutHighTargetTolerance P M q)
noncomputable def timeoutSeparatedFailureEnvelope
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (M L S : ℕ) : Finset ℕ := by
  classical
  exact shellInitialWindowBad M (timeoutHighTolerance P M M) ∪
    ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
      timeoutHighFirstBadSourcesAtRank P K₀ L M S q) ∪
    ((Finset.Icc (L + 1) S).biUnion fun p =>
      timeoutFirstBadSourcesAtRank P K₀ L M S p)
end
end FirstPassageLinearTransport


