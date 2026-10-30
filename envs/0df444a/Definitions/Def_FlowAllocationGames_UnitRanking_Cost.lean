-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_Cost
-- name    : FlowAllocationGames_UnitRanking_Cost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:16:24.164159+00:00
-- url     : https://prove2.me/theorems/126d6616-a3d3-401c-9ca9-b165af2b902a
-- title:
--   Cost counters of a run
-- statement:
--   A run of an algorithm of the mission carries two counters: the **bit cost**, a bit-level running time, and the **step count**, the number of elementary steps. "Polynomial time" is read with both: the bit cost is polynomial in the input size, and the step count is polynomial in $n + m$ alone (strongly polynomial).
--
--   This is part of the cost model in which the mission reads "can be computed in polynomial time" in Theorem 9; the paper itself fixes no machine model.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, Theorem 9, pp. 22–23; p. 5 and p. 39 (strongly polynomial)

import Mathlib

namespace FlowAllocationGames.UnitRanking

/-- **Cost counters of a run.**
Cost model of the mission for "can be computed in polynomial time" in Bertschinger, Hoefer,
Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, Theorem 9, pp. 22–23, and for the
"strongly polynomial time" attributed to it on p. 5 and p. 39.

A run carries two counters: `bits`, the bit-level running time, and `ops`, the number of
elementary steps.

**Formalization Note.** Reading 1 of the mission: "polynomial time" is read with both counters,
bits polynomial in the input size and steps polynomial in `n + m` (strongly polynomial). -/
structure Cost where
  /-- Bit-level running time. -/
  bits : ℕ
  /-- Number of elementary steps. -/
  ops : ℕ

end FlowAllocationGames.UnitRanking


