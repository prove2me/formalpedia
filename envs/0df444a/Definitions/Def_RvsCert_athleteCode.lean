-- Prove2me | Definitions.Def_RvsCert_athleteCode
-- name    : RvsCert_athleteCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:24.145904+00:00
-- url     : https://prove2.me/theorems/fb396988-b28c-4d6e-b0bd-2c36b6fded1d
-- title:
--   Code of an athlete in a race result
-- statement:
--   The athlete $(c,b)$, with country $c\in\{0,\dots,2n-1\}$ and bib number $b\in\{0,\dots,n-1\}$, is written in a race-result entry as the number $1+cn+b\in\{1,\dots,2n^2\}$. The value $0$ is reserved for $\bot$.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, p.1

import Mathlib

namespace RvsCert

/-- **Code of an athlete in a race-result entry** (encoding convention, Section 2, p.1 of
Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: athletes are labelled `(c, b)`). Athlete `(c, b)` is encoded by
`1 + c·n + b ∈ [1, 2n²]`; value `0` is reserved for ⊥. -/
def athleteCode (n : ℕ) (a : Fin (2 * n) × Fin n) : ℕ :=
  1 + (a.1 : ℕ) * n + a.2

end RvsCert


