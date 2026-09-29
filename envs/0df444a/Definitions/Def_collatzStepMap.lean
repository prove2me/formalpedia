-- Prove2me | Definitions.Def_collatzStepMap
-- name    : collatzStepMap
-- status  : Definition
-- author  : @Zexuan Liu
-- created : 2026-09-08T03:50:14.620695+00:00
-- url     : https://prove2.me/theorems/985d110f-b6e9-4e8f-b4e8-421b6c4af77a
-- title:
--   Collatz step map $C(n)$
-- statement:
--   The **Collatz step map** on the natural numbers,
--
--   $$C(n) = \begin{cases} n/2, & n \text{ even},\\ 3n+1, & n \text{ odd}.\end{cases}$$
--
--   The even branch uses natural-number division, so the function is total on $\mathbb{N}$; in particular $C(0)=0$, which is why every statement about the Collatz dynamics carries a positivity hypothesis on the starting value. The Lean declaration is `collatzStep`, character-for-character the definition appearing in the preamble of the mission goal theorem `collatz_conjecture`, packaged here as an importable module so that supporting lemmas and the goal statement share a single Lean constant.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; matches the local definition in the preamble of the prove2.me theorem collatz_conjecture, itself following google-deepmind/formal-conjectures, FormalConjectures/Wikipedia/CollatzConjecture.lean: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/CollatzConjecture.lean

import Mathlib.Algebra.Group.Nat.Even

/-- One step of the Collatz map: an even number is halved, an odd number `n` is sent to
`3 * n + 1`.  Natural-number division is used on the even branch, so the definition is total;
`collatzStep 0 = 0`. -/
def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1


