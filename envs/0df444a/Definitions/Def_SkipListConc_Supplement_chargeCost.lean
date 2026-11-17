-- Prove2me | Definitions.Def_SkipListConc_Supplement_chargeCost
-- name    : SkipListConc_Supplement_chargeCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:48:33.331621+00:00
-- url     : https://prove2.me/theorems/f1773ac5-f409-4e1d-9e55-18c2ce5da584
-- title:
--   Cost $\mathrm{cost}_t(x_t)$ of the search of one operation
-- statement:
--   For an operation sequence $\sigma$ and a position $t$, $\mathrm{cost}_t(x_t)$ is the cost of the search that operation $t$ performs for its target $x_t$ in the skip list of the items present (those inserted at or before $t$): the number of levels it visits plus the number of steps it takes along levels. Every item other than $x_t$ is at its current height, and $x_t$ at its served height $H_{x_t}(f_t-1)$ (with $H_x(0)=1$ for an insertion); heights follow Definition 1.1 without reseeding.
--
--   **Formalization Note** The summand of the published `SkipListConc.totalCost`.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.1, pp.4–5

import Mathlib
import Definitions.Def_SkipListConc_heightAt
import Definitions.Def_SkipListConc_presentAt
import Definitions.Def_SkipListConc_searchCost

namespace SkipListConc.Supplement

/-- The cost `cost_t(x_t)` of the search of operation `t` of `σ` under Definition 1.1 without
reseeding (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §1.1, pp.4–5): the search for `x_t = σ[t]` in the skip list of
the items present (inserted at or before `t`), every item at its height during that search, the
target at its served height (`1` for an insertion).

**Formalization Note** This is the summand of the published `SkipListConc.totalCost`;
positions are 0-based. -/
noncomputable def chargeCost (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (t : Fin σ.length) (ω : Ω) : ℕ :=
  searchCost (presentAt σ t) (fun y => heightAt p ξ σ t y ω) (σ.get t)

end SkipListConc.Supplement


