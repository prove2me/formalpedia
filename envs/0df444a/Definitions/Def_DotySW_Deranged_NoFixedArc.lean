-- Prove2me | Definitions.Def_DotySW_Deranged_NoFixedArc
-- name    : DotySW_Deranged_NoFixedArc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:54.068303+00:00
-- url     : https://prove2.me/theorems/ecf79ed8-8597-4636-97b6-de4981aea321
-- title:
--   An $(r,r)$-diagram with no horizontal edge connecting $i$ to $-i$
-- statement:
--   An $(r,r)$-diagram satisfies this condition when, for every $i$, it has no horizontal edge connecting $i$ to $-i$. These are the diagrams that index the basis of the deranged algebra.
--
--   **Formalization Note** The condition is imposed on both the top row and the bottom row. Under flip, with the signs of the bottom row inverted, such an edge on either row is exactly a fixed point of the permutation.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.2, unnumbered, p. 11

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_Algebra

namespace DotySW.Deranged

open WalledBrauer.Blocks

/-- **An `(r, r)`-diagram with no horizontal edge connecting `i` to `-i`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.2, unnumbered, p. 11.

**Formalization Note** The condition is imposed on the top row and on the bottom row: under flip
with the signs of the bottom row inverted, a fixed point of the permutation is exactly such an edge
on one of the two rows. Position `-i` is `Fin.natAdd r i`. -/
def NoFixedArc {r : ℕ} (D : WalledDiagram r r) : Prop :=
  ∀ i : Fin r, D.1 (Sum.inl (Fin.castAdd r i)) ≠ Sum.inl (Fin.natAdd r i) ∧
    D.1 (Sum.inr (Fin.castAdd r i)) ≠ Sum.inr (Fin.natAdd r i)

end DotySW.Deranged


