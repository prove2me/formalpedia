-- Prove2me | Definitions.Def_SkipListConc_Supplement_costXa
-- name    : SkipListConc_Supplement_costXa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:54:33.492883+00:00
-- url     : https://prove2.me/theorems/482686ff-f0a9-4d97-8eea-fe02d70c8ebe
-- title:
--   $\mathrm{cost}(X)$ without reseeding in the [BDL08] model
-- statement:
--   In the cost model of [BDL08] each step of the finger (forward, up or down) costs one unit and the finger starts at the top of the header, so a search of cost $\mathrm{cost}_t(x_t)$ moves it $\mathrm{cost}_t(x_t)-1$ times; each level by which a height changes costs one unit. Without reseeding heights only rise, so the height changes total $\sum_xH_x(f_x)$ (an initial draw counting as a rise from $0$). For an operation sequence $\sigma$,
--   $$
--   \mathrm{cost}(X)=\sum_t\bigl(\mathrm{cost}_t(x_t)-1\bigr)+\sum_xH_x(f_x).
--   $$
--
--   **Formalization Note** Applied to $\sigma_X$ (the insertions followed by the accesses) every search is counted, insertions included: "on our side their cost is part of the additive term" (p.35).
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Theorem F, p.11; §5.3, p.35

import Mathlib
import Definitions.Def_SkipListConc_heightAt
import Definitions.Def_SkipListConc_presentAt
import Definitions.Def_SkipListConc_searchCost

namespace SkipListConc.Supplement

/-- The cost `cost(X)` of the structure without reseeding in the cost model of [BDL08]
(Theorem F(a)) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Theorem F, p.11, and §5.3, p.35): each step of the finger (forward, up,
down) costs one unit and the finger starts at the top of the header, so the search of operation
`t` moves it `cost_t(x_t) − 1` times; and each level by which a height changes costs one unit.
Without reseeding heights only rise, an initial draw counting as a rise from `0`, so the height
changes total `∑_x H_x(f_x)`.

**Formalization Note** Applied to `σ_X` (the insertions followed by the accesses), every
operation's search is counted, insertions included ("on our side their cost is part of the
additive term", p.35). `cost_t(x_t) ≥ 1`, so the truncated subtraction is exact. -/
noncomputable def costXa (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ω : Ω) : ℕ :=
  (∑ t : Fin σ.length,
      (searchCost (presentAt σ t) (fun y => heightAt p ξ σ t y ω) (σ.get t) - 1)) +
    ∑ x ∈ σ.toFinset, height p ξ x (σ.count x) ω

end SkipListConc.Supplement


