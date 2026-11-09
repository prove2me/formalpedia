-- Prove2me | Definitions.Def_SkipListConc_truncTraj
-- name    : SkipListConc_truncTraj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:53.802605+00:00
-- url     : https://prove2.me/theorems/5bdea724-6def-499f-a777-6c5f4f88d0f8
-- title:
--   Truncated trajectory $T^\ell_y$
-- statement:
--   For $\ell\ge 0$ and an item $y$, the trajectory of $y$ **truncated at $\ell$** is
--   $$
--   T^\ell_y=\bigl(\min(H_y(j),\ell)\bigr)_{0\le j\le f_y},\qquad H_y(0)=1 .
--   $$
--   It records, for every $j$, whether the height after $j$ operations had reached each of the levels $1,\dots,\ell$, and nothing about how far above $\ell$ it went.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §3.3, p.18

import Mathlib
import Definitions.Def_SkipListConc_height

namespace SkipListConc

/-- The trajectory of item `y` truncated at level `ℓ`,
`T^ℓ_y = (min(H_y(j), ℓ))_{0 ≤ j ≤ f_y}`, `H_y(0) = 1` (Kapoor–Tanveer, *Counter-Free
Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256
f82c3d35…6dab6c), §3.3, p.18). -/
noncomputable def truncTraj (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ℓ : ℕ) (y : σ.toFinset) (ω : Ω) :
    Fin (σ.count (y : α) + 1) → ℕ :=
  fun j => min (height p ξ (y : α) j ω) ℓ

end SkipListConc


