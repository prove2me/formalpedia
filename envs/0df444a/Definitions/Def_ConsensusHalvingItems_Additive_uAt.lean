-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_uAt
-- name    : ConsensusHalvingItems_Additive_uAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:26:34.519437+00:00
-- url     : https://prove2.me/theorems/a1e504f1-acb5-4182-af4a-6affd267db70
-- title:
--   Ticked read of an input value $u_i(j)$
-- statement:
--   The input of the algorithm is the matrix of item values $u = (u_i(j))_{i \in N, j \in M}$, where $u_i(j)$ is agent $i$'s utility for the whole item $j$. Reading the entry $u_i(j)$ charges $\operatorname{bitSize}(u_i(j)) + 1$ ticks and returns $u_i(j)$. The algorithm of the mission reads its input only in this way.
--
--   This is part of the cost model in which the mission reads "polynomial-time" in Theorem 2.2; the paper itself fixes no machine model.
--
--   **Formalization Note** Agents are `Fin n` and items `Fin m` (0-based); the values are rationals of any sign.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, §2, p. 4 ("for an item j ∈ M, we sometimes write ui(j) to denote ui({j})")

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_tick
import Definitions.Def_ConsensusHalvingItems_Additive_bitSize

namespace ConsensusHalvingItems.Additive

/-- **Ticked read of one input value `u_i(j)`.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, §2, p. 4: "for an item j ∈ M, we sometimes write ui(j) to denote
ui({j})".

The input of the algorithm is the matrix `u : Fin n → Fin m → ℚ` of item values, `u i j` being
agent `i`'s utility for item `j`. `uAt u i j` charges `bitSize (u i j) + 1` and returns
`u i j`.

**Formalization Note.** The algorithm of the mission reads its input only through this helper.
Agents and items are 0-based (`Fin n`, `Fin m`); values are rationals of any sign (Readings 2
and 4 of the mission). -/
def uAt {n m : ℕ} (u : Fin n → Fin m → ℚ) (i : Fin n) (j : Fin m) : StateM ℕ ℚ := do
  tick (bitSize (u i j) + 1)
  pure (u i j)

end ConsensusHalvingItems.Additive


