-- Prove2me | Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
-- name    : FirstPassageLinearTransport_ShrinkingProfile
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:14:33.659904+00:00
-- url     : https://prove2.me/theorems/16891264-e99c-403a-af8d-02b4e3487dd2
-- title:
--   Shrinking Profile
-- statement:
--   Definitions and structural lemmas for Shrinking Profile, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingProfile.lean

import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
noncomputable def shrinkingSeparatedFailureEnvelope
    (P : ShrinkingBarrierRunData) (M L S : ℕ) : Finset ℕ := by
  classical
  exact shellInitialWindowBad M (shrinkingHighTolerance P M M) ∪
    ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
      shrinkingFirstBadSourcesAtRank P M S q) ∪
    ((Finset.Icc L S).biUnion fun q =>
      shrinkingFirstBadSourcesAtRank P M S q)
end
end FirstPassageLinearTransport


