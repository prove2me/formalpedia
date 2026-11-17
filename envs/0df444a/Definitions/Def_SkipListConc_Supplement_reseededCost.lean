-- Prove2me | Definitions.Def_SkipListConc_Supplement_reseededCost
-- name    : SkipListConc_Supplement_reseededCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:53:11.173579+00:00
-- url     : https://prove2.me/theorems/5ca5cc77-db5f-4032-b5f7-8c9f1458abbd
-- title:
--   Search cost plus rebuild cost of a reseeded structure
-- statement:
--   For a reseeded structure (Definition 1.6), the quantity of Theorem E,
--   $$
--   \sum_t\mathrm{cost}_t(x_t)+(\text{cost of the rebuilds}),
--   $$
--   where the search of operation $t$ runs among the items present, each at its height in the current epoch, and every operation that opens an epoch adds the rebuild cost.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 1.6 and Theorem E, p.10

import Mathlib
import Definitions.Def_SkipListConc_presentAt
import Definitions.Def_SkipListConc_searchCost
import Definitions.Def_SkipListConc_Supplement_rsHeight
import Definitions.Def_SkipListConc_Supplement_rebuildCost

namespace SkipListConc.Supplement

/-- The cost `∑_t cost_t(x_t) + (cost of the rebuilds)` of a reseeded structure (Theorem E)
(Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Definition 1.6 and Theorem E, p.10): the search of every operation `t` among the items
present, each at its height in the current epoch (`rsHeight`), plus the rebuild cost of every
operation that opens an epoch. -/
noncomputable def reseededCost (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ω : Ω) : ℕ :=
  ∑ t : Fin σ.length,
    (searchCost (presentAt σ t) (fun y => rsHeight p ξ σ t y ω) (σ.get t) + rebuildCost p ξ σ t ω)

end SkipListConc.Supplement


