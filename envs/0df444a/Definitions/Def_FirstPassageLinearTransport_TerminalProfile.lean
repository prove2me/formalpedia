-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TerminalProfile
-- name    : FirstPassageLinearTransport_TerminalProfile
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:08:18.470302+00:00
-- url     : https://prove2.me/theorems/5e754ef2-ba69-4772-ae0e-6f39d9d69229
-- title:
--   Terminal Profile
-- statement:
--   Definitions and structural lemmas for Terminal Profile, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
def terminalTailBound (b b' c' : ℝ) (L : ℕ) : ℝ :=
  weightedTailConstant (Real.log 2) c' *
      Real.exp (-(c' * (L : ℝ))) +
    Real.exp b * weightedTailConstant b b' *
      Real.exp (-(b' * (L : ℝ)))
end
end FirstPassageLinearTransport


