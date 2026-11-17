-- Prove2me | Definitions.Def_SkipListConc_Supplement_rsHeight
-- name    : SkipListConc_Supplement_rsHeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:51:14.897333+00:00
-- url     : https://prove2.me/theorems/1a1397ef-2fb3-4d77-896e-0e77e2e0fb49
-- title:
--   Height of an item during a search under reseeding
-- statement:
--   Under epochal reseeding (Definition 1.6), within epoch $r$ the heights follow Definition 1.1 from a fresh initial draw, using randomness of epoch $r$ only. The height of item $y$ during the search of operation $t$ is $H_{(y,r)}(g)$, where $r$ is the epoch of $t$ and $g=\mathrm{reseedCount}(\sigma,t,y)$; the first draw $H_{(y,r)}(1)=J_0+G_0$ is the re-initialization (or the insertion), and $g=0$ gives the conventional height $1$ of an insertion's own search.
--
--   **Formalization Note** The randomness is indexed by $((y,r),j)$, the $j$-th draw of item $y$ in epoch $r$; `IsPromotionNoise` on this index type makes all epochs' draws fresh and independent.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 1.6, p.10, with Definition 1.1, pp.5–6

import Mathlib
import Definitions.Def_SkipListConc_height
import Definitions.Def_SkipListConc_Supplement_reseedCount

namespace SkipListConc.Supplement

/-- The height of item `y` during the search of operation `t` under epochal reseeding
(Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Definition 1.6, p.10, with Definition 1.1, pp.5–6): within epoch `r` the heights follow
Definition 1.1 from a fresh initial draw, using randomness of epoch `r` only.

**Formalization Note** The noise is indexed by `((y, r), j)`: the `j`-th draw of item `y` in
epoch `r`, so all epochs' draws are fresh and independent under `IsPromotionNoise` on the index
type `(α × ℕ) × ℕ`. The height is `height p ξ (y, r) g` with `g = reseedCount σ t y`; draw `1`
is the initial draw `J₀ + G₀` (re-initialization at the epoch start, or the insertion), and
`g = 0` gives the conventional height `1` of an insertion's own search. -/
noncomputable def rsHeight (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (t : ℕ) (y : α) (ω : Ω) : ℕ :=
  height p ξ (y, (epochState σ t).1) (reseedCount σ t y) ω

end SkipListConc.Supplement


