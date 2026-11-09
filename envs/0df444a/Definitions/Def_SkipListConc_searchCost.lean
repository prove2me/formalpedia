-- Prove2me | Definitions.Def_SkipListConc_searchCost
-- name    : SkipListConc_searchCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:38.99947+00:00
-- url     : https://prove2.me/theorems/247a5e3d-139a-44c0-8e36-694eae784af5
-- title:
--   Cost of one skip-list search
-- statement:
--   The **cost of a search** is the number of levels it visits plus the number of steps it takes along a level. A search for $x$ in $(S,h)$ descends from $H_{\max}=\max_{y\in S}h(y)$ to $h(x)$, so
--   $$
--   \mathrm{cost}(x)=\sum_{\ell=h(x)}^{H_{\max}}\bigl(1+\mathrm{steps}_\ell(x)\bigr)=R+\mathrm{hor}(x),\qquad R=H_{\max}-h(x)+1 .
--   $$
--   On Figure 1 of the paper (keys $3,7,12,19,25,31,40$ with heights $1,3,1,4,3,1,2$, target $40$) it gives $3+3=6$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.1, p.4, Figure 1 (p.5)

import Mathlib
import Definitions.Def_SkipListConc_levelSteps

namespace SkipListConc

/-- The cost of one skip-list search (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists:
Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), §1.1, p.4):
"the number of levels it visits plus the number of steps it takes along a level". A search for `x`
descends from level `H_max = max_{y ∈ S} h y` to level `h x`, visiting `R = H_max − h x + 1`
levels, and on each level `ℓ` it takes `levelSteps S h x ℓ` steps.

**Formalization Note** Closed form `∑_{ℓ = h x}^{H_max} (1 + steps on ℓ)`; on Figure 1 (p.5) it
gives `3 + 3 = 6`. -/
def searchCost {α : Type*} [LinearOrder α] (S : Finset α) (h : α → ℕ) (x : α) : ℕ :=
  ∑ ℓ ∈ Finset.Icc (h x) (S.sup h), (1 + levelSteps S h x ℓ)

end SkipListConc


