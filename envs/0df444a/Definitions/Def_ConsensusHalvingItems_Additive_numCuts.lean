-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_numCuts
-- name    : ConsensusHalvingItems_Additive_numCuts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:28:30.372178+00:00
-- url     : https://prove2.me/theorems/951381c8-6b0a-4b6b-abd3-fe00148ef9a9
-- title:
--   Number of cut items
-- statement:
--   An item is **cut** if a positive fraction of it lies in both parts of the partition. For the partition $(x, 1 - x)$ the number of cut items is
--
--   $$
--   \#\{\, j \in M : 0 < x_j \text{ and } 0 < 1 - x_j \,\}.
--   $$
--
--   Theorem 2.2 bounds this number by $\min\{n, m\}$.
--
--   **Formalization Note** The partition is encoded as $(x, 1 - x)$; items `Fin m`.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, Definition 2.1, p. 4 ("An item is said to be cut if there is a positive fraction of it in both parts of the partition")

import Mathlib

namespace ConsensusHalvingItems.Additive

/-- **Number of cut items.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, Definition 2.1, p. 4: "An item is said to be cut if there is a
positive fraction of it in both parts of the partition."

For the partition `(x, 1 - x)`, item `j` is cut when `0 < x j` and `0 < 1 - x j`;
`numCuts x` is the number of cut items.

**Formalization Note.** The partition `(M₁, M₂)` is encoded as `(x, 1 - x)`. -/
def numCuts {m : ℕ} (x : Fin m → ℚ) : ℕ :=
  (Finset.univ.filter fun j => 0 < x j ∧ 0 < 1 - x j).card

end ConsensusHalvingItems.Additive


