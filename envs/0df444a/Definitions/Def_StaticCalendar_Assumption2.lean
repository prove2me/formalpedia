-- Prove2me | Definitions.Def_StaticCalendar_Assumption2
-- name    : StaticCalendar_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:51.70839+00:00
-- url     : https://prove2.me/theorems/ddf6b366-3895-4683-82d6-9b5b76833a26
-- title:
--   Assumption 2: more of the demand is sold at a higher price
-- statement:
--   For all items $i$, feasible assortments $S,S'$, price indices $j,j'$ with $p_j>p_{j'}$, and all $c\in[0,1]$,
--
--   $$
--   \frac{\mathbb E_{Q\sim F_{(i,j,S)}}[\min\{c,Q\}]}{\mathbb E_{Q\sim F_{(i,j,S)}}[Q]}\ \ge\ \frac{\mathbb E_{Q'\sim F_{(i,j',S')}}[\min\{c,Q'\}]}{\mathbb E_{Q'\sim F_{(i,j',S')}}[Q']},
--   $$
--
--   where $F_{(i,j,S)}$ is the marginal law of the quantity of product $(i,j)$ under $D_S$. Read the ratio as the fraction of untruncated demand sold when $c$ units remain: the assumption says this fraction is larger at the higher price. It is the only assumption on fractional demand laws needed for Theorem 1.
--
--   **Formalization Note** The inequality is cross-multiplied. The two forms agree when both means are positive, and the product form reads $0\le0$ when a mean vanishes, where the ratio form is undefined.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Assumption 2, p.13

import Mathlib
import Definitions.Def_StaticCalendar_DemandModel

open MeasureTheory

namespace StaticCalendar

/-- Assumption 2, arXiv:1811.01077v5, p.13: for all items `i`, feasible assortments `S, S'` and
prices `p_j > p_{j'}`, for all `c ∈ [0,1]`, the fraction of untruncated demand sold is larger at the
higher price:
`E_{Q∼F(i,j,S)}[min{c,Q}] / E_{Q∼F(i,j,S)}[Q] ≥ E_{Q'∼F(i,j',S')}[min{c,Q'}] / E_{Q'∼F(i,j',S')}[Q']`.

**Formalization Note.** Cross-multiplied: the ratio form is `0/0` when a mean vanishes. When both
means are positive the two forms are equivalent, and when a mean is `0` the product form holds
with both sides `0`. The expectations are taken under the joint law, whose `(i,j)` marginal is
`F(i,j,S)`. For `(i,j) ∉ S` the inequality reads `0 ≤ 0`. -/
def Assumption2 {n m : ℕ} (I : DemandModel n m) : Prop :=
  ∀ i : Fin n, ∀ S ∈ I.family, ∀ S' ∈ I.family, ∀ j j' : Fin m, I.p j' < I.p j →
    ∀ c ∈ Set.Icc (0 : ℝ) 1,
      (∫ Q, min c (Q (i, j')) ∂I.D S') * I.q S i j ≤ (∫ Q, min c (Q (i, j)) ∂I.D S) * I.q S' i j'

end StaticCalendar


