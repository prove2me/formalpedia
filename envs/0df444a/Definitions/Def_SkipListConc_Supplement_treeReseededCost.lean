-- Prove2me | Definitions.Def_SkipListConc_Supplement_treeReseededCost
-- name    : SkipListConc_Supplement_treeReseededCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:00:29.163382+00:00
-- url     : https://prove2.me/theorems/8c120a9d-8e76-48b0-9c24-4b10250f9a10
-- title:
--   Total tree cost under reseeding
-- statement:
--   Under reseeding the tree redraws every priority at the start of each epoch (Definition 1.6) and is rebuilt from its keys in sorted order as a Cartesian tree in $O(n)$ time. The total tree cost is the sum over all charges of the tree cost with the priorities of the current epoch, plus, at every operation that opens an epoch, the rebuild, one unit per item present.
--
--   **Formalization Note** The $O(n)$ rebuild is fixed as the number of items present before the operation.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Theorem 8.3 and its proof, p.42

import Mathlib
import Definitions.Def_SkipListConc_opCount
import Definitions.Def_SkipListConc_presentAt
import Definitions.Def_SkipListConc_Supplement_rsHeight
import Definitions.Def_SkipListConc_Supplement_rsAfter
import Definitions.Def_SkipListConc_Supplement_treeChargeCost

namespace SkipListConc.Supplement

/-- The total tree cost of a reseeded self-adjusting treap / zip tree (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Theorem 8.3 and its
proof, p.42): the tree redraws every priority at the start of each epoch (Definition 1.6) and is
rebuilt from its keys in sorted order as a Cartesian tree in `O(n)` time; every charge pays
`treeChargeCost` with the priorities of the current epoch (`rsHeight`, after: `rsAfter`), and
every operation that opens an epoch pays the rebuild, one unit per item present.

**Formalization Note** The `O(n)` rebuild is fixed as the number of items present (inserted
before the operation); constant factors are absorbed by the existential constants. -/
noncomputable def treeReseededCost (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ω : Ω) : ℕ :=
  ∑ t : Fin σ.length,
    (treeChargeCost (presentAt σ t) (fun y => rsHeight p ξ σ t y ω) (rsAfter p ξ σ t (σ.get t) ω)
        (σ.get t) (decide (opCount σ (σ.get t) t = 0)) +
      if (epochState σ t).2.2 = 1 then (σ.take t).toFinset.card else 0)

end SkipListConc.Supplement


