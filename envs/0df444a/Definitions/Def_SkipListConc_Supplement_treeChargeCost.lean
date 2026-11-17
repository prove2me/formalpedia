-- Prove2me | Definitions.Def_SkipListConc_Supplement_treeChargeCost
-- name    : SkipListConc_Supplement_treeChargeCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:58:21.948209+00:00
-- url     : https://prove2.me/theorems/04dc22e5-a55e-4d6e-805d-6bf2865021a4
-- title:
--   Tree cost of one charge (search plus restructuring)
-- statement:
--   In the self-adjusting treap and zip tree, the tree cost of a charge is the number of nodes the tree search visits plus $q_t$, the number of ancestors the target $x$ moves past when its priority rises from its served value $h(x)$ to $h'$ (the treap passes each by one rotation; the zip tree's unzip handles each node once):
--
--   1. **access:** the search visits $x$ and its proper ancestors in the equivalent tree on $S$; $x$ moves past those ancestors $y$ that its new priority beats ($h'>h(y)$, or $h'=h(y)$ and $x<y$);
--   2. **insertion:** the unsuccessful search visits the nodes of its path in the tree on $S\setminus\{x\}$; $x$ is placed below them and moves past those its priority $h'$ beats.
--
--   **Formalization Note** Treap and zip tree have the same shape (the equivalent tree) after every operation, so one cost covers both; the factor $c_T$ between this count and pointer updates is absorbed by the existential constants.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §8, pp.41–42 (Lemma 8.2)

import Mathlib
import Definitions.Def_SkipListConc_Supplement_treeAncestors

namespace SkipListConc.Supplement

/-- The tree cost of one charge in the self-adjusting treap or zip tree (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §8, pp.41–42,
Lemma 8.2): the nodes the tree search visits plus `q_t`, the number of ancestors the target `x`
moves past when its priority rises from its served value `h x` to `h'` (the treap passes each by
one rotation of unit cost; the zip tree's unzip handles each node once).

* access (`isInsert = false`): the search visits `x` and its proper ancestors in the equivalent
  tree on `S` with priorities `h`; `x` moves past those ancestors `y` that its new priority
  beats (`h' > h y`, or `h' = h y` and `x < y`);
* insertion (`isInsert = true`): the unsuccessful search visits the nodes of its path in the tree
  on `S ∖ {x}`; `x` is placed below them and moves past those its priority `h'` beats.

**Formalization Note** The treap and the zip tree have the same shape (the equivalent tree) and
restore it after each promotion, so one cost covers both; the constant factor between rotations
and pointer updates (`c_T`) is absorbed by the theorems' existential constants. -/
def treeChargeCost {α : Type*} [LinearOrder α] (S : Finset α) (h : α → ℕ) (h' : ℕ) (x : α)
    (isInsert : Bool) : ℕ :=
  let A := if isInsert then treeAncestors (S.erase x) h x else treeAncestors S h x
  (if isInsert then 0 else 1) + A.card + (A.filter fun y => h y < h' ∨ (h y = h' ∧ x < y)).card

end SkipListConc.Supplement


