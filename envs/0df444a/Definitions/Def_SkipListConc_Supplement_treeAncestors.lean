-- Prove2me | Definitions.Def_SkipListConc_Supplement_treeAncestors
-- name    : SkipListConc_Supplement_treeAncestors
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:57:51.149148+00:00
-- url     : https://prove2.me/theorems/8945d5e0-79bb-43d2-89a5-ac188c77a69e
-- title:
--   Ancestors in the equivalent tree (treap / zip tree shape)
-- statement:
--   The **equivalent tree** of a skip list on keys $S$ with heights $h$ is the unique binary search tree on $S$ that is heap-ordered by priority $h$, ties broken in favour of smaller keys. A key $y\neq x$ is a proper ancestor of $x$ iff $y$ beats every other key $w$ of $S$ in the closed key interval between $x$ and $y$, where $y$ beats $w$ iff $h(y)>h(w)$, or $h(y)=h(w)$ and $y<w$. For $x\notin S$ the same set is the set of nodes an unsuccessful search for $x$ visits.
--
--   **Formalization Note** Checked on Figure 4: the search for 40 visits 19, 25, 40 and the search for 31 visits 19, 25, 40, 31.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §8, p.40

import Mathlib

namespace SkipListConc.Supplement

/-- The proper ancestors of `x` in the equivalent tree of a skip list (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §8, p.40): the
unique binary search tree on the keys `S` that is heap-ordered by priority `h` (the skip-list
height), ties broken in favour of smaller keys. Key `y ≠ x` is a proper ancestor of `x` iff `y`
beats every other key `w` of `S` in the closed key interval between `x` and `y`, where `y` beats
`w` iff `h y > h w`, or `h y = h w` and `y < w`.

**Formalization Note** For `x ∉ S`, `treeAncestors S h x` is the set of nodes an (unsuccessful)
search for `x` visits in the tree on `S`; checked on Figure 4 (the search for 40 visits 19, 25,
40). -/
def treeAncestors {α : Type*} [LinearOrder α] (S : Finset α) (h : α → ℕ) (x : α) : Finset α :=
  (S.erase x).filter fun y => ∀ w ∈ S, min x y ≤ w → w ≤ max x y → w ≠ y →
    (h w < h y ∨ (h w = h y ∧ y < w))

end SkipListConc.Supplement


