-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
-- name    : FirstPassageLinearTransport_TwoRegimeClock
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:09:50.636427+00:00
-- url     : https://prove2.me/theorems/7c88de18-3fae-41f3-a0ff-4be5fa5b77f8
-- title:
--   Two Regime Clock
-- statement:
--   Definitions and structural lemmas for Two Regime Clock, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeClock.lean

import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
set_option autoImplicit true
namespace FirstPassageLinearTransport
noncomputable section
def twoRegimeClockPotential (rHi rLo : ℝ) (S q : ℕ) : ℝ :=
  if S ≤ q then
    (q : ℝ) / (1 - rHi) + (S : ℝ) / (1 - rLo)
  else
    (q : ℝ) / (1 - rLo)
inductive TwoRegimeRankTrace
    (rHi rLo : ℝ) (S M : ℕ) : ℕ → ℕ → Prop
  | first {h q : ℕ}
      (hhM : h ≤ M)
      (hq : (q : ℝ) ≤ rHi * (M : ℝ)) :
      TwoRegimeRankTrace rHi rLo S M h q
  | next {elapsed qPrev m h q : ℕ}
      (htrace : TwoRegimeRankTrace rHi rLo S M elapsed qPrev)
      (hmPrev : m ≤ qPrev) (hhm : h ≤ m)
      (hq : if S ≤ m then (q : ℝ) ≤ rHi * (m : ℝ)
        else (q : ℝ) ≤ rLo * (m : ℝ)) :
      TwoRegimeRankTrace rHi rLo S M (elapsed + h) q
noncomputable def twoRegimeHorizon
    (rHi rLo : ℚ) (S M : ℕ) : ℕ :=
  ⌈((M : ℝ) / (1 - (rHi : ℝ)) +
      (S : ℝ) / (1 - (rLo : ℝ)))⌉₊
end
end FirstPassageLinearTransport


