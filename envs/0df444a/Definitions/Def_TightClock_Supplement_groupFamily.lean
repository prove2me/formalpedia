-- Prove2me | Definitions.Def_TightClock_Supplement_groupFamily
-- name    : TightClock_Supplement_groupFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:07:54.701329+00:00
-- url     : https://prove2.me/theorems/1f3ce19f-b9af-4f7c-bc1d-cfc9ce14b464
-- title:
--   Feasibility family of disjoint groups
-- statement:
--   For publicly known groups $G_1,\dots,G_k$ of bidders, a set of bidders is feasible if and only if it is contained in one group:
--
--   $$\mathcal F_G=\{S:\ S\subseteq G_j\text{ for some }j\}.$$
--
--   When the groups are pairwise disjoint, $f(v)=\max_j v(G_j)$ on nonnegative profiles.
--
--   **Formalization Note** The empty set is included explicitly, so the family is nonempty also when there are no groups (no bidders).
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §4, p.15 (PDF p.18)

import Mathlib

set_option autoImplicit false

namespace TightClock.Supplement

/-- The feasibility family of disjoint groups: a set of bidders is feasible iff it is contained in
one group. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §4, p.15 (PDF 18): "the bidders are partitioned into publicly known, pairwise
disjoint groups G1, . . . , Gk, and a set of bidders is feasible if and only if it is contained in
one group."

**Formalization Note** The groups are a `Finset` of sets of bidders. `∅` is included explicitly so
that the family is nonempty also when there are no groups (no bidders). -/
def groupFamily {n : ℕ} (Gs : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  insert ∅ (Gs.biUnion Finset.powerset)

end TightClock.Supplement


