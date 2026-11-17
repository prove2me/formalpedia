-- Prove2me | Definitions.Def_SkipListConc_Supplement_ruleTotalCost
-- name    : SkipListConc_Supplement_ruleTotalCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:49:48.721376+00:00
-- url     : https://prove2.me/theorems/f8edbe88-aa01-4798-821c-50807b323d80
-- title:
--   Total search cost under an abstract promotion rule
-- statement:
--   For a height process $H$ and an operation sequence $\sigma$, the total search cost is $\sum_t\mathrm{cost}_t(x_t)$, where the search of operation $t$ runs in the skip list of the items present, item $y$ at height $H_y(j)$ with $j$ the number of operations on $y$ strictly before $t$ (so the target is at its served height), and at height $1$ when $j=0$ (the convention for the search of an insertion).
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.1, pp.4–5; Theorem D, p.9

import Mathlib
import Definitions.Def_SkipListConc_opCount
import Definitions.Def_SkipListConc_presentAt
import Definitions.Def_SkipListConc_searchCost

namespace SkipListConc.Supplement

/-- The total search cost `∑_t cost_t(x_t)` of an operation sequence `σ` under an abstract
height process `H` (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §1.1, pp.4–5, as used in Theorem D, p.9): operation `t`
searches for `x_t = σ[t]` among the items present, item `y` at height `H_y(j)` with `j` the
number of operations on `y` strictly before `t` (the target at its served height), and height
`1` when `j = 0` (the convention `H_x(0) = 1` for the search of an insertion, p.5). -/
noncomputable def ruleTotalCost {α Ω : Type*} [LinearOrder α] (H : α → ℕ → Ω → ℕ)
    (σ : List α) (ω : Ω) : ℕ :=
  ∑ t : Fin σ.length, searchCost (presentAt σ t)
    (fun y => if opCount σ y t = 0 then 1 else H y (opCount σ y t) ω) (σ.get t)

end SkipListConc.Supplement


