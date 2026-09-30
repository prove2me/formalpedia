-- Prove2me | Definitions.Def_SeymourMFMC_Binary_tau
-- name    : SeymourMFMC_Binary_tau
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T02:42:59.849986+00:00
-- url     : https://prove2.me/theorems/0ebc7822-110a-4075-bbce-ffe0615f9132
-- title:
--   τ(L): the minimum cardinality of a member of the blocker
-- statement:
--   For a clutter $\mathbf L$, $\tau(\mathbf L)$ is the minimum cardinality of a member of the blocker:
--
--   $$
--   \tau(\mathbf L) = \min_{B \in b(\mathbf L)} |B| .
--   $$
--
--   It is the "min-cut" value: a clutter packs when it has $\tau(\mathbf L)$ pairwise disjoint members.
--
--   **Formalization Note** The paper leaves $\tau(\{\emptyset\})$ undefined, because $b(\{\emptyset\}) = \emptyset$. In Lean that case gets the junk value $0$. Every statement of this mission that reads $\tau$ either excludes $\{\emptyset\}$ or is vacuous on it.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 192, Section 1

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_blocker

namespace SeymourMFMC.Binary

/-- `tau L` is `τ(L)`, the minimum cardinality of a member of the blocker `b(L)` (Seymour 1977,
p. 192). The paper leaves `τ({∅})` undefined (then `b(L) = ∅`); here that case gets the junk
value `0`, and every statement reading `τ` excludes it or is vacuous on it. -/
def tau {α : Type*} [DecidableEq α] (L : Finset (Finset α)) : ℕ :=
  if h : (blocker L).Nonempty then ((blocker L).image Finset.card).min' (h.image _) else 0

end SeymourMFMC.Binary


