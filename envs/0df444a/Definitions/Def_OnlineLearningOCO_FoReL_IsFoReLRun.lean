-- Prove2me | Definitions.Def_OnlineLearningOCO_FoReL_IsFoReLRun
-- name    : OnlineLearningOCO_FoReL_IsFoReLRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:24.410122+00:00
-- url     : https://prove2.me/theorems/322a4dcf-8345-4ca9-b69b-e7ba6ff16094
-- title:
--   Follow-the-Regularized-Leader run (§2.3, p. 127)
-- statement:
--   Let $S$ be a set, let $f_1, f_2, \dots : S \to \mathbb R$ be loss functions and let $R : S \to \mathbb R$ be a **regularization function**. A sequence $w_1, w_2, \dots$ is a run of **Follow-the-Regularized-Leader** (FoReL) if for every round $t \ge 1$,
--
--   $$
--   w_t \in \operatorname*{argmin}_{w \in S} \Big( \sum_{i=1}^{t-1} f_i(w) + R(w) \Big),
--   $$
--
--   that is, $w_t \in S$ and $\sum_{i=1}^{t-1} f_i(w_t) + R(w_t) \le \sum_{i=1}^{t-1} f_i(v) + R(v)$ for every $v \in S$. In round $1$ the sum is empty, so $w_1$ minimizes $R$ over $S$.
--
--   FoReL is the algorithm whose regret the mission bounds; with $R = 0$ it is Follow-the-Leader.
--
--   **Formalization Note** Rounds are numbered from $1$, and $w_0$, $f_0$ are unused. The argmin is a predicate on the whole trajectory, not a chosen minimizer, so every tie-breaking rule among minimizers gives a run ("break ties arbitrarily", p. 124). Losses and regularizer are functions on the ambient type; only their values on $S$ enter the predicate.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 127, §2.3, Follow-the-Regularized-Leader (FoReL)

import Mathlib

namespace OnlineLearningOCO.FoReL

/-- Follow-the-Regularized-Leader (Shalev-Shwartz, *Online Learning and Online Convex
Optimization*, FnT ML 4(2) (2011), §2.3, p. 127): `w` is a run of FoReL on the losses `f` over the
set `S` with regularization function `R` if, for every round `t ≥ 1`,
`w_t ∈ argmin_{w ∈ S} ∑_{i=1}^{t-1} f_i(w) + R(w)`.
Rounds are 1-based and `w 0`, `f 0` are unused. At `t = 1` the sum is empty, so `w 1` minimizes
`R` over `S`. The argmin is a predicate on the trajectory: every tie-breaking rule among
minimizers gives a run. -/
def IsFoReLRun {E : Type*} (S : Set E) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E) : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    w t ∈ S ∧ ∀ v ∈ S,
      (∑ i ∈ Finset.Ico 1 t, f i (w t)) + R (w t) ≤ (∑ i ∈ Finset.Ico 1 t, f i v) + R v

end OnlineLearningOCO.FoReL


