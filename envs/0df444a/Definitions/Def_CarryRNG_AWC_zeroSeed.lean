-- Prove2me | Definitions.Def_CarryRNG_AWC_zeroSeed
-- name    : CarryRNG_AWC_zeroSeed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:44.913345+00:00
-- url     : https://prove2.me/theorems/8ec034a7-ae30-49b9-8dfa-279bc22fb09e
-- title:
--   The trivial seed $(0,\dots,0,0)$ (p. 472)
-- statement:
--   For a base $b \ge 2$ and a lag $r$, the **zero seed** is the state
--
--   $$(0, \dots, 0, 0),$$
--
--   all $r$ digits equal to $0$ and carry $0$. It is one of the two **trivial seeds** of Section 4.5 for both the add-with-carry and subtract-with-borrow generators.
--
--   **Formalization Note** The definition takes the proof of $2 \le b$ as an argument, matching the base of the generator.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 472, Section 4.5 ("the trivial seed vectors (0, ..., 0, 0) and (b - 1, ..., b - 1, 1)")

import Definitions.Def_CarryRNG_AWC_State

namespace CarryRNG.AWC

/-- The trivial seed `(0, …, 0, 0)`: all digits zero and carry zero (p. 472). -/
def zeroSeed (b r : ℕ) (hb : 2 ≤ b) : State b r :=
  ⟨fun _ => ⟨0, by omega⟩, 0⟩

end CarryRNG.AWC


