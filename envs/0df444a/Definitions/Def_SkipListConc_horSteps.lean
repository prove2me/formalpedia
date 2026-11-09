-- Prove2me | Definitions.Def_SkipListConc_horSteps
-- name    : SkipListConc_horSteps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:46.840899+00:00
-- url     : https://prove2.me/theorems/416f4949-14c1-450f-a9fe-87bd228daf42
-- title:
--   Horizontal steps $\mathrm{hor}(x)$ of one search
-- statement:
--   The number of **horizontal steps** of a search for $x$ in a skip list $(S,h)$ is
--   $$
--   \mathrm{hor}(x)=\sum_{\ell=h(x)}^{H_{\max}} \mathrm{steps}_\ell(x),\qquad H_{\max}=\max_{y\in S}h(y),
--   $$
--   the steps taken along the $R=H_{\max}-h(x)+1$ levels the search visits.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §4.2, p.20; §1.1, p.4

import Mathlib
import Definitions.Def_SkipListConc_levelSteps

namespace SkipListConc

/-- The number `hor(x)` of horizontal steps of a search for `x` (Kapoor–Tanveer, *Counter-Free
Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256
f82c3d35…6dab6c), §4.2, p.20, and §1.1, p.4): the steps along the levels `h x, …, H_max` that the
search visits, where `H_max = max_{y ∈ S} h y`. -/
def horSteps {α : Type*} [LinearOrder α] (S : Finset α) (h : α → ℕ) (x : α) : ℕ :=
  ∑ ℓ ∈ Finset.Icc (h x) (S.sup h), levelSteps S h x ℓ

end SkipListConc


