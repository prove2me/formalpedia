-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_bitSizeZ
-- name    : FlowAllocationGames_UnitRanking_bitSizeZ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:17:34.303257+00:00
-- url     : https://prove2.me/theorems/25c04b20-3749-49c6-98fc-f27ef32f47ae
-- title:
--   Bit size of an integer
-- statement:
--   The **bit size** of an integer $z$ is $\operatorname{size}(|z|) + 2$: the binary digits of $|z|$ plus a sign bit and one more, so that $0$ has bit size $2$.
--
--   This is part of the cost model in which the mission reads "can be computed in polynomial time" in Theorem 9; the paper itself fixes no machine model.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, Theorem 9, pp. 22–23

import Mathlib

namespace FlowAllocationGames.UnitRanking

/-- **Bit size of an integer.**
Cost model of the mission for Theorem 9 of Bertschinger, Hoefer, Schmand, *Flow Allocation Games*,
arXiv:1908.01714v3, pp. 22–23.

`bitSizeZ z = size |z| + 2`: the binary digits of `|z|`, one sign bit and one more, so that
`bitSizeZ 0 = 2`. -/
def bitSizeZ (z : ℤ) : ℕ := Nat.size z.natAbs + 2

end FlowAllocationGames.UnitRanking


