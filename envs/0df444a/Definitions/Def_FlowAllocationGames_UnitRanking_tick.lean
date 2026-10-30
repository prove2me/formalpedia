-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_tick
-- name    : FlowAllocationGames_UnitRanking_tick
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:17:02.087002+00:00
-- url     : https://prove2.me/theorems/dcb84871-4266-430a-aa19-9a1d1a4f0b63
-- title:
--   One step of the cost model
-- statement:
--   The algorithms of the mission are programs that carry the two cost counters. The primitive $\mathsf{tick}(c)$ adds $c$ to the bit cost and $1$ to the step count. The cost of a run started from zero counters is its final state.
--
--   Every algorithm of the mission obeys one convention: each arithmetic operation or comparison on integer data is charged a cost quadratic in the bit sizes of its operands; each input number read is charged its bit size; every iteration of every loop and every recursive call ticks at least once, and scanning a list ticks once per element; the uncharged work between two ticks is index bookkeeping of size polynomial in $n + m$. The algorithms never read the counters.
--
--   This is part of the cost model in which the mission reads "can be computed in polynomial time" in Theorem 9; the paper itself fixes no machine model.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, Theorem 9, pp. 22–23

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost

namespace FlowAllocationGames.UnitRanking

/-- **Charging one step of cost `c`.**
Cost model of the mission for "can be computed in polynomial time" in Bertschinger, Hoefer,
Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, Theorem 9, pp. 22–23.

The algorithms of the mission are programs in the state monad `StateM Cost`. `tick c` adds `c` to
the bit counter and `1` to the step counter. The cost of a run started at `⟨0, 0⟩` is the final
state.

**Formalization Note.** The convention binding every algorithm of the mission: every arithmetic
operation or comparison on integer data goes through `zadd`, `zsub`, `zmul`, `zlt`, which charge
`opCost a b`, quadratic in the bit sizes of the operands; every entry of the input is read through
`bAt`, `cAt`, `tailAt`, `headAt`, which charge its bit size; every iteration of every loop and
every recursive call ticks at least once, and every scan of a list ticks once per element; the
unticked code between two ticks does only index bookkeeping (array positions, node and edge indices,
lists of at most `n + 1` indices, arrays of size at most `m + 2n + 1`), whose cost is polynomial in
`n + m`, and never computes with flow or capacity values. The algorithms never read the counters,
so the cost of a run does not depend on the start state. -/
def tick (c : ℕ) : StateM Cost Unit := modify fun s => ⟨s.bits + c, s.ops + 1⟩

end FlowAllocationGames.UnitRanking


