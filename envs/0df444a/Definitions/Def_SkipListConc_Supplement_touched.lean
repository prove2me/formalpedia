-- Prove2me | Definitions.Def_SkipListConc_Supplement_touched
-- name    : SkipListConc_Supplement_touched
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:56:15.614192+00:00
-- url     : https://prove2.me/theorems/726532ae-7335-4368-88bc-3e461e6ca096
-- title:
--   Items a skip-list search touches
-- statement:
--   The items a skip-list search for $x$ touches are those its path steps onto on some level $\ell$ between $h(x)$ and the top level, $x$ included (stepped onto on level $h(x)$). On level $\ell$ the search steps onto the nodes $y\le x$ with $h(y)\ge\ell$ such that no node $w$ with $y\le w\le x$ has height $\ge\ell+1$, which are the nodes counted by the published `levelSteps`.
--
--   **Formalization Note** Checked on Figure 1: the search for 40 touches 19, 25, 40, and the search for 31 touches 19, 25, 31 (caption of Figure 4).
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.2, p.11; §5.3, p.35

import Mathlib

namespace SkipListConc.Supplement

/-- The items a skip-list search for `x` touches (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §1.2, p.11, and §5.3, p.35): the
items its path steps onto on some level `ℓ` between `h x` and the top `max h`, `x` included (it is
stepped onto on level `h x`). These are exactly the items counted by the published
`SkipListConc.levelSteps S h x ℓ` on some visited level `ℓ`.

**Formalization Note** As in `levelSteps`: on level `ℓ` the search steps onto the nodes `y ≤ x`
with `h y ≥ ℓ` such that no node `w` with `y ≤ w ≤ x` has height `≥ ℓ + 1`. -/
def touched {α : Type*} [LinearOrder α] (S : Finset α) (h : α → ℕ) (x : α) : Finset α :=
  S.filter fun y => ∃ ℓ ∈ Finset.Icc (h x) (S.sup h),
    y ≤ x ∧ ℓ ≤ h y ∧ ∀ w ∈ S, y ≤ w → w ≤ x → h w ≤ ℓ

end SkipListConc.Supplement


