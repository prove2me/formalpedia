-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
-- name    : FirstPassageLinearTransport_TimeoutFirstBad
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:18:08.03804+00:00
-- url     : https://prove2.me/theorems/4dc61c2d-3056-4435-b551-b012e07b87b6
-- title:
--   Timeout First Bad
-- statement:
--   Definitions and structural lemmas for Timeout First Bad, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutFirstBad.lean

import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
set_option autoImplicit true
namespace FirstPassageLinearTransport
noncomputable section
noncomputable def timeoutLandingBad
    (K₀ : ℝ) (L p : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell (p - 1)).filter (LowStageTimeout K₀ L (p - 1))
noncomputable def timeoutFirstBadSourcesAtRank
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (L M S p : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n =>
    ∃ h : ℕ, TimeoutRecertificationRun P K₀ L M S n h p ∧
      LowStageTimeout K₀ L (p - 1) (orbit h n)
end
end FirstPassageLinearTransport


