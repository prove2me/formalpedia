-- Prove2me | Definitions.Def_SkipListConc_totalCost
-- name    : SkipListConc_totalCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:30.238077+00:00
-- url     : https://prove2.me/theorems/5d8a2f51-c6dc-4fef-83ba-781ba15f20c6
-- title:
--   Total search cost $\sum_t \mathrm{cost}_t(x_t)$ of a sequence
-- statement:
--   For an operation sequence $\sigma$ of length $F$ and a realization of the promotion randomness, the **total search cost** is
--   $$
--   \sum_{t=1}^{F}\mathrm{cost}_t(x_t),
--   $$
--   where operation $t$ searches for $x_t$ in the skip list of the items present at time $t$ (those inserted at or before $t$), each item at its height during that search: $H_y(f_y(t))$ for $y\ne x_t$ and the served height $s_t$ for the target. Only the searches are charged, not the relinking work of promotions.
--
--   **Formalization Note** Positions are 0-based.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.1, pp.4–5; Theorem C, p.8

import Mathlib
import Definitions.Def_SkipListConc_heightAt
import Definitions.Def_SkipListConc_presentAt
import Definitions.Def_SkipListConc_searchCost

namespace SkipListConc

/-- The total search cost `∑_t cost_t(x_t)` of an operation sequence `σ` (Kapoor–Tanveer,
*Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript
(sha256 f82c3d35…6dab6c), §1.1, pp.4–5, and Theorem C, p.8). Operation `t` searches for
`x_t = σ[t]` in the skip list of the items present (inserted at or before `t`), every item `y` at
its height during that search, `H_y` after its operations strictly before `t` (the target at its
served height).

**Formalization Note** Only the searches are charged, not the relinking of promotions (p.8). -/
noncomputable def totalCost (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ω : Ω) : ℕ :=
  ∑ t : Fin σ.length, searchCost (presentAt σ t) (fun y => heightAt p ξ σ t y ω) (σ.get t)

end SkipListConc


