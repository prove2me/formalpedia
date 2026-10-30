-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_halve
-- name    : ConsensusHalvingItems_Additive_halve
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:34:00.723531+00:00
-- url     : https://prove2.me/theorems/da6cc264-69b7-4066-8212-d478b06464a9
-- title:
--   The algorithm of Theorem 2.2
-- statement:
--   The consensus-halving algorithm from the proof of Theorem 2.2. On the value matrix $u$ of $n$ agents and $m$ items:
--
--   1. if $m \le n$, it returns $x_j = 1/2$ for every item (charging $m + 1$ ticks);
--   2. otherwise it sets $x_1 = \dots = x_m = 1/2$ and $T = \emptyset$ (Steps 1 and 2), runs the while loop of Step 3, and outputs the final $x$ (Step 4).
--
--   The output $x$ describes the partition $(x, 1 - x)$ of the items. Theorem 2.2 asserts that it is a consensus halving with at most $\min\{n, m\}$ cut items, computed in polynomial time.
--
--   **Formalization Note** The paper treats $n \ge m$ separately and runs the loop when $n \le m$; at $n = m$ both are correct and the first branch is taken. The free choices of the paper (the solution $y$ of footnote 5 and the argmin of Step 3b) are fixed as in the definitions of the Gaussian elimination and of one iteration.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, ¶1 and Steps 1–4, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_tick
import Definitions.Def_ConsensusHalvingItems_Additive_halveLoop

namespace ConsensusHalvingItems.Additive

/-- **The algorithm of Theorem 2.2.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, p. 5: "If n ≥ m, a partition that divides every
item in half is clearly a consensus halving and makes m = min{n, m} cuts. We therefore assume
from now on that n ≤ m and describe a polynomial-time algorithm …", Steps 1–4.

On the value matrix `u` of `n` agents and `m` items, `halve u`

1. if `m ≤ n`, charges `m + 1` ticks and returns the point `x_j = 1/2` for every `j`;
2. otherwise starts from `x_1 = ⋯ = x_m = 1/2` and `T = ∅` (Steps 1–2) and runs the while loop
   of Step 3 (`halveLoop` with fuel `m + 1`), returning its output (Step 4).

The output `x` describes the partition `(x, 1 - x)` of the items.

**Formalization Note.** The paper's "assume n ≤ m" branch is taken here for `n < m`; for
`n = m` both branches are correct and the first is used. Readings 1–5 of the mission apply: bit
model, rational input, the witness algorithm with its fixed choices, any sign, 0-based indices. -/
def halve {n m : ℕ} (u : Fin n → Fin m → ℚ) : StateM ℕ (Fin m → ℚ) :=
  if m ≤ n then do
    tick (m + 1)
    pure fun _ => 1 / 2
  else halveLoop u (m + 1) ∅ (fun _ => 1 / 2)

end ConsensusHalvingItems.Additive


