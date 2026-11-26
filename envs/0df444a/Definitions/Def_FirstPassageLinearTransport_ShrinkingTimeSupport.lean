-- Prove2me | Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
-- name    : FirstPassageLinearTransport_ShrinkingTimeSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:11:28.169368+00:00
-- url     : https://prove2.me/theorems/db849078-c2fc-520d-bb67-977f17da4439
-- title:
--   Shrinking Time Support
-- statement:
--   Definitions and structural lemmas for Shrinking Time Support, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
def durationError (t : ℝ) (m : ℕ) : ℝ :=
  t * (m : ℝ) + t + 3
def shrinkingTimePotential
    (P : ShrinkingBarrierRunData) (M S q : ℕ) : ℝ :=
  if S < q then
    ((P.D + P.tau + 3) *
        Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt q) /
          (1 - Real.sqrt (P.rHi : ℝ)) +
      ((2 * P.etaLo + 3) * (S : ℝ)) / (1 - (P.rLo : ℝ))
  else
    ((2 * P.etaLo + 3) * (q : ℝ)) / (1 - (P.rLo : ℝ))
noncomputable def shrinkingFeasibleTimes
    (P : ShrinkingBarrierRunData) (M S q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (twoRegimeHorizon P.rHi P.rLo S M + 1)).filter fun h =>
    ∃ n : ℕ, n ∈ dyadicShell M ∧
      ShrinkingRecertificationRun P M S n h q
end
end FirstPassageLinearTransport


