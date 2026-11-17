-- Prove2me | Definitions.Def_SkipListConc_Supplement_rebuildCost
-- name    : SkipListConc_Supplement_rebuildCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:52:23.94364+00:00
-- url     : https://prove2.me/theorems/14cd1563-b259-44e6-862f-9dbd6e807e92
-- title:
--   Cost of the rebuild at the start of an epoch
-- statement:
--   Under epochal reseeding the skip list is rebuilt at the start of each epoch from the new heights, and "the work of the rebuild is counted as cost". The rebuild gives each item $y$ present a fresh height $H_y$ and links it into that many levels, $O(1+H_y)$ work per item. The rebuild cost at an operation $t$ that opens an epoch is
--   $$
--   \sum_{y\ \text{present before } t}\bigl(1+H_y\bigr),
--   $$
--   and $0$ at an operation that does not open an epoch. The first epoch's rebuild has no items and costs $0$.
--
--   **Formalization Note** The $O(\cdot)$ of the source is fixed as the unit cost $1+H_y$; constant factors are absorbed by the theorems' existential constants.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 1.6, p.10; proof of Lemma 5.3, p.33

import Mathlib
import Definitions.Def_SkipListConc_height
import Definitions.Def_SkipListConc_Supplement_epochState

namespace SkipListConc.Supplement

/-- The cost of the rebuild at operation `t` under epochal reseeding (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Definition 1.6,
p.10, and the proof of Lemma 5.3, p.33): if `t` opens an epoch `r`, every item present (inserted
before `t`) gets a fresh height `H_y` and is linked into that many levels, `O(1 + H_y)` work per
item; the rebuild cost is `∑_y (1 + H_y)`. Otherwise it is `0`.

**Formalization Note** The fresh height of `y` in epoch `r` is draw `1` of the index `(y, r)`,
`height p ξ (y, r) 1`. The first epoch's rebuild has no items and costs `0`. The `O(·)` of the
source is fixed as the unit cost `1 + H_y`; constant factors are absorbed by the theorems'
existential constants. -/
noncomputable def rebuildCost (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (t : ℕ) (ω : Ω) : ℕ :=
  if (epochState σ t).2.2 = 1 then
    ∑ y ∈ (σ.take t).toFinset, (1 + height p ξ (y, (epochState σ t).1) 1 ω)
  else 0

end SkipListConc.Supplement


