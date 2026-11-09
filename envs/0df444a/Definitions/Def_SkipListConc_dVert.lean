-- Prove2me | Definitions.Def_SkipListConc_dVert
-- name    : SkipListConc_dVert
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:30.266616+00:00
-- url     : https://prove2.me/theorems/2b1a8d3f-dc10-4e4b-9325-bf1b20b2071a
-- title:
--   Vertical cost $D_x(L)$ of one item below a cutoff
-- statement:
--   Fix an item $x$, a number $f$ of searches for it and an integer cutoff $L\ge 1$. The $j$-th search for $x$ finds it at height $H_x(j-1)$, with $H_x(0)=1$, so the **vertical cost of $x$ below $L$** is
--   $$
--   D_x(L)=\sum_{j=1}^{f}\bigl(L-H_x(j-1)+1\bigr)_+ .
--   $$
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §4.5.1, p.24

import Mathlib
import Definitions.Def_SkipListConc_height

namespace SkipListConc

/-- The vertical cost of item `x` below the cutoff `L` (Kapoor–Tanveer, *Counter-Free
Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256
f82c3d35…6dab6c), §4.5.1, p.24): over `f` searches for `x`, the `j`-th finding it at
`H_x(j − 1)` (with `H_x(0) = 1`),
`D_x(L) = ∑_{j=1}^{f} (L − H_x(j − 1) + 1)_+`.

**Formalization Note** The positive part is truncated subtraction in `ℕ`. -/
noncomputable def dVert (p : ℝ) {K : ℕ} {α Ω : Type*}
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (x : α) (f L : ℕ) (ω : Ω) : ℕ :=
  ∑ j ∈ Finset.range f, (L + 1 - height p ξ x j ω)

end SkipListConc


