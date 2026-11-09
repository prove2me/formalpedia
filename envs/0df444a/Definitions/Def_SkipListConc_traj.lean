-- Prove2me | Definitions.Def_SkipListConc_traj
-- name    : SkipListConc_traj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:40.651127+00:00
-- url     : https://prove2.me/theorems/1f14d680-568f-486e-836c-323122bc5336
-- title:
--   Height trajectory of an item
-- statement:
--   The **height trajectory** of an item $y$ of $\sigma$ is $(H_y(j))_{0\le j\le f_y}$, with $H_y(0)=1$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §3.3, p.18

import Mathlib
import Definitions.Def_SkipListConc_height

namespace SkipListConc

/-- The height trajectory `(H_y(j))_{0 ≤ j ≤ f_y}` of an item `y` of `σ`, with `H_y(0) = 1`
(Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §3.3, p.18). -/
noncomputable def traj (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (y : σ.toFinset) (ω : Ω) :
    Fin (σ.count (y : α) + 1) → ℕ :=
  fun j => height p ξ (y : α) j ω

end SkipListConc


