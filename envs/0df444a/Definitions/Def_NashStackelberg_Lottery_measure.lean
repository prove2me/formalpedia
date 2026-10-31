-- Prove2me | Definitions.Def_NashStackelberg_Lottery_measure
-- name    : NashStackelberg_Lottery_measure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:52.018833+00:00
-- url     : https://prove2.me/theorems/53fffca9-b6de-44cf-b6be-0ad5d0874b00
-- title:
--   The mixed strategy $\sum_j p_j\delta_{\hat x_j}$ of a finite lottery
-- statement:
--   The mixed strategy induced by a finite lottery $(\hat x,p)$ is the measure
--   $$
--   \sum_{j=1}^{k} p_j\,\delta_{\hat x_j}
--   $$
--   on $\mathbb R^V$, where $\delta_{\hat x}$ is the point mass at $\hat x$. When the weights are nonnegative and sum to one it is a probability measure; this is how "player $i$ plays $\hat x^i_j$ with probability $p^i_j$" in Theorem 4 is read.
--
--   **Formalization Note** Weights enter through $\max(p_j,0)$ as extended nonnegative reals; for the lotteries of Algorithm 1 the weights are nonnegative, so this changes nothing.
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Theorem 4, p.12

import Mathlib
import Definitions.Def_NashStackelberg_Lottery

open MeasureTheory

namespace NashStackelberg

/-- **The mixed strategy of a finite lottery** (Carvalho, Dragotto, Feijoo, Lodi &
Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, Theorem 4, p.12: "each player
i plays the strategy x̂ⁱⱼ with probability pⁱⱼ").

The measure `Σⱼ pⱼ δ_{x̂ⱼ}` on `V → ℝ`.

**Formalization Note.** Weights enter as `ENNReal.ofReal pⱼ`; where the lottery is used the
weights are nonnegative and sum to one, so this is a probability measure. -/
noncomputable def Lottery.measure {V : Type*} (L : Lottery V) : Measure (V → ℝ) :=
  ∑ j, ENNReal.ofReal (L.prob j) • Measure.dirac (L.pts j)

end NashStackelberg


