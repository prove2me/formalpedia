-- Prove2me | Definitions.Def_SkipListConc_Supplement_treeCharge
-- name    : SkipListConc_Supplement_treeCharge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:58:58.663097+00:00
-- url     : https://prove2.me/theorems/9a3d2142-58c2-4e71-ba25-df0e1918fd16
-- title:
--   Tree cost of the charge at one operation
-- statement:
--   In the self-adjusting treap / zip tree without reseeding, the priorities follow Definition 1.1 as the heights of a skip list run on the same sequence would. The tree cost of operation $t$ is the tree cost of one charge on the items present, with the current priorities (the target at its served priority) and the target's priority after the operation $H_{x_t}(f_t)$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §8, pp.41–42

import Mathlib
import Definitions.Def_SkipListConc_heightAt
import Definitions.Def_SkipListConc_presentAt
import Definitions.Def_SkipListConc_Supplement_treeChargeCost

namespace SkipListConc.Supplement

/-- The tree cost of the charge at operation `t` in the self-adjusting treap / zip tree without
reseeding (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §8, pp.41–42): priorities are the heights of Definition 1.1 (`heightAt`, the
target at its served priority), the target's priority after the operation is
`H_{x_t}(f_t)`, and the cost is `treeChargeCost` on the items present. -/
noncomputable def treeCharge (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (t : Fin σ.length) (ω : Ω) : ℕ :=
  treeChargeCost (presentAt σ t) (fun y => heightAt p ξ σ t y ω)
    (height p ξ (σ.get t) (opCount σ (σ.get t) t + 1) ω) (σ.get t)
    (decide (opCount σ (σ.get t) t = 0))

end SkipListConc.Supplement


