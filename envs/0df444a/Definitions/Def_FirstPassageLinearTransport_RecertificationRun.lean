-- Prove2me | Definitions.Def_FirstPassageLinearTransport_RecertificationRun
-- name    : FirstPassageLinearTransport_RecertificationRun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:06:53.522005+00:00
-- url     : https://prove2.me/theorems/09be351e-000e-5119-84ee-6ac43aaddd93
-- title:
--   Recertification Run
-- statement:
--   Definitions and structural lemmas for Recertification Run, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationRun.lean

import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
set_option autoImplicit true
namespace FirstPassageLinearTransport
noncomputable section
inductive RecertificationRun {r : ℚ} {eta : ℝ}
    (p : StageSetup (r : ℝ) eta) (n : ℕ) : ℕ → ℕ → Prop
  | first {m : ℕ}
      (hm0 : p.M0 ≤ m)
      (hnShell : n ∈ dyadicShell m)
      (hnGood : n ∈ initialWindowGood eta) :
      RecertificationRun p n (stageLength p n) (rationalTargetRank r m)
  | next {elapsed qprev m : ℕ}
      (hrun : RecertificationRun p n elapsed qprev)
      (hm0 : p.M0 ≤ m)
      (hsourceShell : orbit elapsed n ∈ dyadicShell m)
      (hsourceGood : orbit elapsed n ∈ initialWindowGood eta) :
      RecertificationRun p n
        (elapsed + stageLength p (orbit elapsed n))
        (rationalTargetRank r m)
end
end FirstPassageLinearTransport


