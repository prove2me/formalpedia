-- Prove2me | Definitions.Def_SkipListConc_Supplement_IsWeaklyBounded
-- name    : SkipListConc_Supplement_IsWeaklyBounded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:55:58.823046+00:00
-- url     : https://prove2.me/theorems/49baf1b7-ba41-45b0-8b14-ec53fe737e55
-- title:
--   Weakly $B$-bounded skip list
-- statement:
--   A skip list on an item set $S$ with heights $h$ is **weakly $B$-bounded** if, for every $i$, its top $i$ levels together hold at most
--   $$
--   \sum_{j=0}^{i}B^j
--   $$
--   items, where the top level is the greatest height $\max_{y\in S}h(y)$ and item $y$ lies in the top $i$ levels iff $h(y)\ge\max h-i+1$.
--
--   **Formalization Note** The membership condition is written $\max h+1\le h(y)+i$ to avoid natural-number subtraction.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §5.3, p.35, after [BDL08]

import Mathlib

namespace SkipListConc.Supplement

/-- A skip list on the item set `S` with heights `h` is weakly `B`-bounded (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §5.3,
p.35, after [BDL08]) if its top `i` levels together hold at most `∑_{j=0}^{i} B^j` items, for every
`i`; the top level is the greatest height `max_{y ∈ S} h y`.

**Formalization Note** Item `y` lies in the top `i` levels iff `h y ≥ max h − i + 1`, written
`max h + 1 ≤ h y + i` to avoid natural-number subtraction. -/
def IsWeaklyBounded {α : Type*} (B : ℕ) (S : Finset α) (h : α → ℕ) : Prop :=
  ∀ i : ℕ, (S.filter fun y => S.sup h + 1 ≤ h y + i).card ≤ ∑ j ∈ Finset.range (i + 1), B ^ j

end SkipListConc.Supplement


