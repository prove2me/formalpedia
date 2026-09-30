-- Prove2me | Definitions.Def_SeymourMFMC_Binary_IsBinary
-- name    : SeymourMFMC_Binary_IsBinary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T02:01:24.348801+00:00
-- url     : https://prove2.me/theorems/5966759a-afa0-48d4-b999-91f3365f3042
-- title:
--   Binary clutter, via (3.2)(ii): |A ∩ B| odd for A ∈ L, B ∈ b(L)
-- statement:
--   A clutter $\mathbf L$ is **binary** if every member of $\mathbf L$ meets every member of its blocker in an odd number of elements:
--
--   $$
--   |A \cap B| \text{ is odd} \qquad \text{for all } A \in \mathbf L,\ B \in b(\mathbf L).
--   $$
--
--   Path collections, cut collections, odd-circuit collections of graphs and $Q_6$ are binary clutters. The paper's main theorem characterizes the Mengerian binary clutters.
--
--   **Formalization Note** The paper defines a binary clutter as a port $\Omega(M)$ of a binary matroid $M$ (p. 200) and quotes (3.2) [15, 28], without proof, for the equivalence of that definition with condition (ii) above for every clutter. Mathlib at this revision has no matroids representable over GF(2), so (3.2)(ii) is taken as the definition.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 200, Section 3, (3.2)(ii)

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_blocker

namespace SeymourMFMC.Binary

/-- `IsBinary L`: `L` is a **binary clutter** (Seymour 1977, p. 200), in the form of (3.2)(ii):
every member `A ∈ L` and every member `B ∈ b(L)` of the blocker meet in an odd number of
elements. The paper defines binary clutters as ports `Ω(M)` of binary matroids `M` and quotes
(3.2) [15, 28] (not proved there) for the equivalence of that definition with (ii) for every
clutter; Mathlib at this revision has no GF(2)-representable matroids, so (3.2)(ii) is taken as
the definition. -/
def IsBinary {α : Type*} [DecidableEq α] (L : Finset (Finset α)) : Prop :=
  ∀ A ∈ L, ∀ B ∈ blocker L, Odd (A ∩ B).card

end SeymourMFMC.Binary


