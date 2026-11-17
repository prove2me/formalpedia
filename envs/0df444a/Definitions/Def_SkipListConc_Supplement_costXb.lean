-- Prove2me | Definitions.Def_SkipListConc_Supplement_costXb
-- name    : SkipListConc_Supplement_costXb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:55:45.266358+00:00
-- url     : https://prove2.me/theorems/a33c860a-4a04-47ea-b0fe-45f86f5681bb
-- title:
--   $\mathrm{cost}(X)$ under reseeding in the [BDL08] model
-- statement:
--   For a reseeded structure, the cost in the model of [BDL08]: the finger moves $\mathrm{cost}_t(x_t)-1$ of every search (with the heights of the current epoch), plus the rebuild costs, plus every level by which a height changes (a rebuild redraw counting $|\text{new}-\text{old}|$, an insertion draw its height).
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Theorem F, p.11; §5.3, p.35

import Mathlib
import Definitions.Def_SkipListConc_presentAt
import Definitions.Def_SkipListConc_searchCost
import Definitions.Def_SkipListConc_Supplement_rsHeight
import Definitions.Def_SkipListConc_Supplement_rebuildCost
import Definitions.Def_SkipListConc_Supplement_rsHeightChange

namespace SkipListConc.Supplement

/-- The cost `cost(X)` of the reseeded structure in the cost model of [BDL08] (Theorem F(b))
(Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Theorem F, p.11, and §5.3, p.35): the finger moves `cost_t(x_t) − 1` of every search
(heights of the current epoch), the rebuild costs, and every level by which a height changes
(redraws at epoch starts counted as `|new − old|`, insertion draws as their height). -/
noncomputable def costXb (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ω : Ω) : ℕ :=
  ∑ t : Fin σ.length,
    ((searchCost (presentAt σ t) (fun y => rsHeight p ξ σ t y ω) (σ.get t) - 1) +
      rebuildCost p ξ σ t ω + rsHeightChange p ξ σ t ω)

end SkipListConc.Supplement


