-- Prove2me | Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
-- name    : FirstPassageLinearTransport_ShrinkingFirstBad
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:13:27.750601+00:00
-- url     : https://prove2.me/theorems/da595b0a-8d2c-5851-98fc-9c9a45019288
-- title:
--   Shrinking First Bad
-- statement:
--   Definitions and structural lemmas for Shrinking First Bad, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingFirstBad.lean

import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
def shrinkingTargetTolerance
    (P : ShrinkingBarrierRunData) (M S q : ℕ) : ℝ :=
  if S ≤ q - 1 then shrinkingHighTolerance P M (q - 1) else P.etaLo
noncomputable def shrinkingFirstBadSourcesAtRank
    (P : ShrinkingBarrierRunData) (M S q : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n =>
    ∃ h : ℕ, ShrinkingRecertificationRun P M S n h q ∧
      orbit h n ∈ landingBad q (shrinkingTargetTolerance P M S q)
end
end FirstPassageLinearTransport


