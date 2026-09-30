-- Prove2me | Definitions.Def_SeymourMFMC_Binary_IsCycle
-- name    : SeymourMFMC_Binary_IsCycle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T02:10:40.676733+00:00
-- url     : https://prove2.me/theorems/0119b630-2dba-430e-8c17-345a3683656c
-- title:
--   Cycle of a binary clutter: Z ⊆ E(L) with |Z ∩ B| even for all B ∈ b(L)
-- statement:
--   A set $Z$ is a **cycle** of the clutter $\mathbf L$ if $Z \subseteq E(\mathbf L)$ and
--
--   $$
--   |Z \cap B| \text{ is even} \qquad \text{for every } B \in b(\mathbf L).
--   $$
--
--   For a binary clutter $\mathbf L = \Omega(M)$, with $M$ a connected binary matroid, these are the cycles (disjoint unions of circuits) of $M$ avoiding $\Omega$. This auxiliary notion defines the circuits of $\mathbf L$.
--
--   **Formalization Note** The paper does not name this notion. One inclusion is (3.6)(ii), the other is (3.6)(iii)(a) (p. 202).
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 202, (3.6)(ii),(iii)(a) (auxiliary)

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_blocker

namespace SeymourMFMC.Binary

/-- `IsCycle L Z`: `Z ⊆ E(L)` and `Z` has even intersection with every member of the blocker
`b(L)`. For a binary clutter `L = Ω(M)` with `M` a connected binary matroid, these are exactly
the cycles (disjoint unions of circuits) of `M` avoiding `Ω`, by Seymour 1977 (3.6)(ii),(iii)(a),
p. 202. Auxiliary to `IsCircuit`. -/
def IsCycle {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (Z : Finset α) : Prop :=
  Z ⊆ ground L ∧ ∀ B ∈ blocker L, Even (Z ∩ B).card

instance {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (Z : Finset α) :
    Decidable (IsCycle L Z) := by
  unfold IsCycle; infer_instance

end SeymourMFMC.Binary


