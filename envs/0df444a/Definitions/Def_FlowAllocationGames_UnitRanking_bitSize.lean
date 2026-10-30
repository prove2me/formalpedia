-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_bitSize
-- name    : FlowAllocationGames_UnitRanking_bitSize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:17:17.209685+00:00
-- url     : https://prove2.me/theorems/79be0e1b-3c51-43d8-9d5b-34ee9abf48bf
-- title:
--   Bit size of a natural number
-- statement:
--   The **bit size** of a natural number $k$ is $\operatorname{size}(k) + 1$, where $\operatorname{size}(k)$ is the number of binary digits of $k$ (with $\operatorname{size}(0) = 0$). For example, the bit size of $0$ is $1$ and that of $5$ is $4$.
--
--   This is part of the cost model in which the mission reads "can be computed in polynomial time" in Theorem 9; the paper itself fixes no machine model.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, p. 9 (binary encoding); Theorem 9, pp. 22–23

import Mathlib

namespace FlowAllocationGames.UnitRanking

/-- **Bit size of a natural number.**
Cost model of the mission; Bertschinger, Hoefer, Schmand, *Flow Allocation Games*,
arXiv:1908.01714v3, §2.1, p. 9: "all numbers in the input, i.e., all bv and ce, are integer numbers
in binary encoding."

`bitSize k = size k + 1`, where `size k` is the number of binary digits of `k` (`size 0 = 0`).

**Formalization Note.** `bitSize 0 = 1`, so every input number costs at least one bit. -/
def bitSize (k : ℕ) : ℕ := Nat.size k + 1

end FlowAllocationGames.UnitRanking


