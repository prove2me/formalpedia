-- Prove2me | Definitions.Def_MulticastPoS_nonresidual
-- name    : MulticastPoS_nonresidual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:51.385177+00:00
-- url     : https://prove2.me/theorems/344ff87e-9583-4d0b-96c6-e9b0fb017480
-- title:
--   Nonresidual groups $G^+$
-- statement:
--   Let $\pi$ be a partition of the players (equivalently, of the source occurrences) into groups, and let $g_0$ be the residual group, if there is one. The **nonresidual groups** are
--
--   $$
--   G^+=\{\,g\in\pi : g\ne g_0\,\}.
--   $$
--
--   Only nonresidual groups choose a representative.
--
--   **Formalization Note** Source occurrences are identified with players, and "at most one residual group" is an optional group.
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 4.1, p.8; Section 5.1, p.9

import Mathlib

namespace MulticastPoS

/-- The nonresidual groups `G⁺` (Huang–Yuan, *An O(log log n) Upper Bound on the Price of
Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript (sha256
dd0e08d0…f6d4), Section 4.1, p.8 and Section 5.1, p.9): the groups of the partition `π` of the
players other than the residual group `g₀`, if there is one.

**Formalization Note** Source occurrences are identified with players (`oᵢ ↔ i`, p.4), so a
grouping is a partition of the player set; "at most one residual group" is an `Option`. -/
def nonresidual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : Finpartition (Finset.univ : Finset ι)) (g₀ : Option (Finset ι)) : Finset (Finset ι) :=
  π.parts.filter (fun g => some g ≠ g₀)

end MulticastPoS


