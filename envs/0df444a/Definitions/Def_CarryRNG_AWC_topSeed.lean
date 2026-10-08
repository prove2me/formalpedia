-- Prove2me | Definitions.Def_CarryRNG_AWC_topSeed
-- name    : CarryRNG_AWC_topSeed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:45.882983+00:00
-- url     : https://prove2.me/theorems/02f7b145-694e-4a40-af52-79127b9c6809
-- title:
--   The trivial seed $(b-1,\dots,b-1,1)$ (p. 472)
-- statement:
--   For a base $b \ge 2$ and a lag $r$, the **top seed** is the state
--
--   $$(b-1, \dots, b-1, 1),$$
--
--   all $r$ digits equal to $b - 1$ and carry $1$. It is the second **trivial seed** of Section 4.5 for both the add-with-carry and subtract-with-borrow generators.
--
--   **Formalization Note** The definition takes the proof of $2 \le b$ as an argument; it is needed to form the digit $b - 1$.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 472, Section 4.5 ("the trivial seed vectors (0, ..., 0, 0) and (b - 1, ..., b - 1, 1)")

import Definitions.Def_CarryRNG_AWC_State

namespace CarryRNG.AWC

/-- The trivial seed `(b - 1, …, b - 1, 1)`: all digits `b - 1` and carry one (p. 472). -/
def topSeed (b r : ℕ) (hb : 2 ≤ b) : State b r :=
  ⟨fun _ => ⟨b - 1, by omega⟩, 1⟩

end CarryRNG.AWC


