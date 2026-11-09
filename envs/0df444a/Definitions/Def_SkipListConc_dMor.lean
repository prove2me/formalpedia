-- Prove2me | Definitions.Def_SkipListConc_dMor
-- name    : SkipListConc_dMor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:30.000458+00:00
-- url     : https://prove2.me/theorems/86a4bac4-e261-4a7f-ab1f-46e5f76a4395
-- title:
--   Morris count $D^{\mathrm{Mor}}_x(L)$
-- statement:
--   The same sum for the Morris chain, with $M_x(0)=1$:
--   $$
--   D^{\mathrm{Mor}}_x(L)=\sum_{j=1}^{f}\bigl(L-M_x(j-1)+1\bigr)_+ .
--   $$
--   Since $H_x\ge M_x$, it dominates $D_x(L)$ on every outcome.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §4.5.1, p.24

import Mathlib
import Definitions.Def_SkipListConc_morris

namespace SkipListConc

/-- The Morris count below the cutoff `L` (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip
Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), §4.5.1,
p.24): `D^Mor_x(L) = ∑_{j=1}^{f} (L − M_x(j − 1) + 1)_+`, with `M_x(0) = 1`.

**Formalization Note** The positive part is truncated subtraction in `ℕ`. -/
noncomputable def dMor (p : ℝ) {K : ℕ} {α Ω : Type*}
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (x : α) (f L : ℕ) (ω : Ω) : ℕ :=
  ∑ j ∈ Finset.range f, (L + 1 - morris p ξ x j ω)

end SkipListConc


