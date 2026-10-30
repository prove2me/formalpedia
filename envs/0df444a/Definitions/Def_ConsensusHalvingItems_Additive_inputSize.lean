-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_inputSize
-- name    : ConsensusHalvingItems_Additive_inputSize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:27:06.130179+00:00
-- url     : https://prove2.me/theorems/dc0b84a7-4776-4052-8206-ed3099a3f7b2
-- title:
--   Size of an instance
-- statement:
--   An instance with $n$ agents and $m$ items is the matrix $u$ of rational item values $u_i(j)$. Its **size** is
--
--   $$
--   |u| = n + m + \sum_{i=1}^{n} \sum_{j=1}^{m} \operatorname{bitSize}(u_i(j)),
--   $$
--
--   the length of its binary encoding up to a constant factor. An algorithm runs in **polynomial time** when its running time is at most $C(|u| + 1)^k$ for constants $C, k$ independent of the instance.
--
--   This is part of the cost model in which the mission reads "polynomial-time" in Theorem 2.2; the paper itself fixes no machine model.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, Theorem 2.2, p. 4 ("polynomial-time algorithm")

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_bitSize

namespace ConsensusHalvingItems.Additive

/-- **Size of an instance.**
Cost model of the mission for "polynomial-time" in Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1,
Theorem 2.2, p. 4.

An instance with `n` agents and `m` items is the matrix `u : Fin n → Fin m → ℚ` of the values
`u_i(j)`. Its size is

  `inputSize u = n + m + ∑_{i} ∑_{j} bitSize (u i j)`,

the length of its binary encoding up to a constant factor. "Polynomial time" means a running time
bounded by a polynomial in `inputSize u`.

**Formalization Note.** The summands `n` and `m` make the size count the agents and items even
when `n = 0` or `m = 0`. -/
def inputSize {n m : ℕ} (u : Fin n → Fin m → ℚ) : ℕ :=
  n + m + ∑ i, ∑ j, bitSize (u i j)

end ConsensusHalvingItems.Additive


