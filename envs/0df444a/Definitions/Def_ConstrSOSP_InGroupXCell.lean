-- Prove2me | Definitions.Def_ConstrSOSP_InGroupXCell
-- name    : ConstrSOSP_InGroupXCell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:37.095828+00:00
-- url     : https://prove2.me/theorems/866b2975-63c9-4536-a7e0-9dfe92ee3757
-- title:
--   Group X cells
-- statement:
--   A point lies in a **Group X cell** if it lies in $\mathrm{Box}(6k-3,6k+2)$, $\mathrm{Box}(6k-2,6k+2)$ or $\mathrm{Box}(6k-1,6k+2)$ for some Iter solution $k\in$ Solutions: the cells at the top of the blue column of $k$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), end of §5.4.3, p.49

import Mathlib
import Definitions.Def_ConstrSOSP_InSolutions

namespace ConstrSOSP

/-- **The Group X cells** (arXiv:2604.02285, 2 Nov 2026, end of §5.4.3, p.49: "the small boxes
Box(6k* − 3, 6k* + 2), Box(6k* − 2, 6k* + 2) and Box(6k* − 1, 6k* + 2) which only exist on the
blue columns that correspond to Iter solutions k*. We classify such boxes into the Group X").

`InGroupXCell C u` holds iff for some Iter solution `k ∈ Solutions` the point `u` lies in
`Box(6k − r, 6k + 2) = [6k − r, 6k − r + 1] × [6k + 2, 6k + 3]` for some `r ∈ {1, 2, 3}`. -/
def InGroupXCell (C : Circuit) (u : Fin 2 → ℝ) : Prop :=
  ∃ k : ℕ, InSolutions C k ∧ ∃ r : ℕ, 1 ≤ r ∧ r ≤ 3 ∧
    (6 * k - r : ℝ) ≤ u 0 ∧ u 0 ≤ (6 * k - r + 1 : ℝ) ∧ (6 * k + 2 : ℝ) ≤ u 1 ∧
    u 1 ≤ (6 * k + 3 : ℝ)

end ConstrSOSP


