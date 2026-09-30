-- Prove2me | Definitions.Def_SeymourMFMC_Binary_blocker
-- name    : SeymourMFMC_Binary_blocker
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T01:06:41.497974+00:00
-- url     : https://prove2.me/theorems/1c71164c-9e48-4840-8cc6-140045109956
-- title:
--   b(L): the blocker of a clutter, the minimal subsets of E(L) meeting every member
-- statement:
--   The **blocker** $b(\mathbf L)$ of a clutter $\mathbf L$ is the collection of *minimal* subsets of $E(\mathbf L)$ which intersect each member of $\mathbf L$:
--
--   $$
--   b(\mathbf L) = \{ B \subseteq E(\mathbf L) : B \cap A \neq \emptyset \ \forall A \in \mathbf L, \text{ and no proper subset of } B \text{ has this property} \}.
--   $$
--
--   Thus $b(\emptyset) = \{\emptyset\}$ and $b(\{\emptyset\}) = \emptyset$. The blocker is a clutter, and by Edmonds and Fulkerson $b(b(\mathbf L)) = \mathbf L$; the minimum cardinality of its members is $\tau(\mathbf L)$, the "min-cut" side of the max-flow min-cut property.
--
--   **Formalization Note** Both conditions are part of the definition: $B \subseteq E(\mathbf L)$ (the filter runs over the powerset of $E(\mathbf L)$) and minimality (no strict subset of $B$ meets $\mathbf L$).
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 192, Section 1

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_Meets

namespace SeymourMFMC.Binary

/-- `blocker L` is the **blocker** `b(L)` of `L` (Seymour 1977, p. 192): the collection of
*minimal* subsets of `E(L)` which intersect each member of `L`. Here `B ∈ blocker L` iff
`B ⊆ ground L`, `B` meets every member of `L`, and no proper subset of `B` meets every member of
`L`. In particular `blocker ∅ = {∅}` and `blocker {∅} = ∅`. -/
def blocker {α : Type*} [DecidableEq α] (L : Finset (Finset α)) : Finset (Finset α) :=
  (ground L).powerset.filter (fun B => Meets L B ∧ ∀ B' ∈ B.ssubsets, ¬ Meets L B')

end SeymourMFMC.Binary


