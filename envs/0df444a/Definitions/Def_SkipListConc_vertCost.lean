-- Prove2me | Definitions.Def_SkipListConc_vertCost
-- name    : SkipListConc_vertCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:26.9804+00:00
-- url     : https://prove2.me/theorems/5f9a9ab4-7986-48fb-b64a-c374992d7b02
-- title:
--   Total vertical cost $D(L)=\sum_x D_x(L)$
-- statement:
--   For an operation sequence $\sigma$ and a cutoff $L$, the **total vertical cost below $L$** is
--   $$
--   D(L)=\sum_x D_x(L),
--   $$
--   the sum over the distinct items $x$ of $\sigma$, each with $f=f_x$ searches.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §4.5.1, p.24; Lemma 4.7, p.25

import Mathlib
import Definitions.Def_SkipListConc_dVert

namespace SkipListConc

/-- The total vertical cost below the cutoff `L`, `D(L) = ∑_x D_x(L)` with `f = f_x` (Kapoor–Tanveer,
*Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript
(sha256 f82c3d35…6dab6c), §4.5.1, p.24, and Lemma 4.7, p.25), the sum over the distinct items of
`σ`. -/
noncomputable def vertCost (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (L : ℕ) (ω : Ω) : ℕ :=
  ∑ x ∈ σ.toFinset, dVert p ξ x (σ.count x) L ω

end SkipListConc


