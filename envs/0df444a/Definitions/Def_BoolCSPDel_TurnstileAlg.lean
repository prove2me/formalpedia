-- Prove2me | Definitions.Def_BoolCSPDel_TurnstileAlg
-- name    : BoolCSPDel_TurnstileAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:48.185094+00:00
-- url     : https://prove2.me/theorems/a71be4b1-8c43-4e78-ba69-64ae9fac9ad6
-- title:
--   Strict-turnstile streams and the one-pass automaton of the lower bounds
-- statement:
--   A stream is a list of unit updates, each inserting or deleting one copy of an element of a universe $U$. Its frequency vector starts at zero. The stream is **strict turnstile** if every prefix frequency vector is nonnegative, and its prefix multiplicities are at most $\mu$ if every prefix frequency is at most $\mu$.
--
--   A **one-pass automaton** has a state set $S$ and, given a seed $\omega$, an initial state, a transition for each update and an output map. Its memory is $\log_2|S|$ bits.
--
--   **Formalization Note** This is the most general reasonable class: one automaton for each $n$, arbitrary maps, and a persistent seed that is not charged. The lower bounds hold against all of it. The machine of the upper bound is a special case, with configurations as states.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), §3.1, p.17

import Mathlib

namespace BoolCSPDel

/-- **Turnstile streams and the lower-bound algorithm model.** Bandekar, Sharma, Velusamy, STOC 2027
submission (manuscript sha256 15f83519…), §3.1, p.17: "A unit update inserts or deletes one copy of a
constraint. A stream starts from the zero frequency vector and is strict turnstile if every prefix
frequency vector is nonnegative."

The frequency vector of a stream `s` over a universe `U`; `true` inserts, `false` deletes. -/
def freq {U : Type} [DecidableEq U] (s : List (U × Bool)) (C : U) : ℤ :=
  (s.map fun u => if u.1 = C then (if u.2 then (1 : ℤ) else -1) else 0).sum

/-- Strict turnstile: every prefix frequency vector is nonnegative. -/
def IsLegal {U : Type} [DecidableEq U] (s : List (U × Bool)) : Prop :=
  ∀ p, p <+: s → ∀ C, 0 ≤ freq p C

/-- Every prefix multiplicity is at most `μ`. -/
def BoundedBy {U : Type} [DecidableEq U] (μ : ℕ) (s : List (U × Bool)) : Prop :=
  ∀ p, p <+: s → ∀ C, freq p C ≤ μ

/-- A randomized one-pass algorithm on `n` fixed, for the lower bounds.

**Formalization Note.** One automaton per stream universe, with arbitrary transition and output maps,
a persistent seed `ω` read throughout and not charged, and memory `log₂ |S|`
(`CosDensity.memoryBits`). This is the most general reasonable class, so the lower bounds are as
strong as possible; the machine of the upper bound is a special case (states = configurations). -/
structure TurnstileAlg (U Ω S O : Type) where
  /-- Initial state from the seed. -/
  init : Ω → S
  /-- One update. -/
  step : Ω → U × Bool → S → S
  /-- Output from the final state. -/
  out : Ω → S → O

/-- The state after one pass over `s`. -/
def TurnstileAlg.run {U Ω S O : Type} (A : TurnstileAlg U Ω S O) (ω : Ω) (s : List (U × Bool)) : S :=
  s.foldl (fun st u => A.step ω u st) (A.init ω)

end BoolCSPDel


