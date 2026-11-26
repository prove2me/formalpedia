-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
-- name    : FirstPassageLinearTransport_TwoRegimeRun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:08:48.986893+00:00
-- url     : https://prove2.me/theorems/2ddfdc47-ea1b-5380-88c7-ace6fb49d7e1
-- title:
--   Two Regime Run
-- statement:
--   Definitions and structural lemmas for Two Regime Run, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeRun.lean

import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
set_option autoImplicit true
namespace FirstPassageLinearTransport
noncomputable section
inductive MixedRecertificationRun (rStar : ℚ) (n : ℕ) : ℕ → ℕ → Prop
  | first {r : ℚ} {eta : ℝ} (p : StageSetup (r : ℝ) eta)
      {m : ℕ}
      (hStar : rStar ≤ r)
      (hm0 : p.M0 ≤ m)
      (hnShell : n ∈ dyadicShell m)
      (hnGood : n ∈ initialWindowGood eta) :
      MixedRecertificationRun rStar n
        (stageLength p n) (rationalTargetRank r m)
  | next {elapsed qprev : ℕ} (hrun : MixedRecertificationRun rStar n elapsed qprev)
      {r : ℚ} {eta : ℝ} (p : StageSetup (r : ℝ) eta)
      {m : ℕ}
      (hStar : rStar ≤ r)
      (hm0 : p.M0 ≤ m)
      (hsourceShell : orbit elapsed n ∈ dyadicShell m)
      (hsourceGood : orbit elapsed n ∈ initialWindowGood eta)
      (hgap : rationalTargetRank r m < qprev) :
      MixedRecertificationRun rStar n
        (elapsed + stageLength p (orbit elapsed n))
        (rationalTargetRank r m)
end
end FirstPassageLinearTransport


