-- Prove2me | Definitions.Def_MulticastPoS_Selection
-- name    : MulticastPoS_Selection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:40.89368+00:00
-- url     : https://prove2.me/theorems/2163082c-bdc1-4a2b-b38d-00c9915d6061
-- title:
--   Representative selections
-- statement:
--   Given a partition $\pi$ of the players with residual group $g_0$, a **representative selection** chooses one member $p_g\in g$ of every nonresidual group $g\in G^+$. The set of representative selections is the product $\prod_{g\in G^+} g$.
--
--   Choosing each representative uniformly at random, independently for different groups, is the uniform distribution on this finite set.
--
--   **Formalization Note** A dependent function type, finite and nonempty (the groups of a partition are nonempty).
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 4.2, pp.8–9

import Mathlib
import Definitions.Def_MulticastPoS_nonresidual

namespace MulticastPoS

/-- Representative selections (Huang–Yuan, *An O(log log n) Upper Bound on the Price of Stability
for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript (sha256 dd0e08d0…f6d4),
Section 4.2, pp.8–9): a choice of one representative `p_g ∈ g` for every nonresidual group `g`.

**Formalization Note** A finite type (a dependent function type); it is nonempty because the parts
of a `Finpartition` are nonempty. Choosing each representative uniformly and independently across
groups (p.8) is the uniform distribution on this type. -/
abbrev Selection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : Finpartition (Finset.univ : Finset ι)) (g₀ : Option (Finset ι)) : Type _ :=
  ∀ g : ↥(nonresidual π g₀), ↥g.1

end MulticastPoS


