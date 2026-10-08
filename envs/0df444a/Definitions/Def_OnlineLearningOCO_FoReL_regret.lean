-- Prove2me | Definitions.Def_OnlineLearningOCO_FoReL_regret
-- name    : OnlineLearningOCO_FoReL_regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:21.50036+00:00
-- url     : https://prove2.me/theorems/139c8fab-0e29-4312-87b7-e59d087b791a
-- title:
--   Regret of an online learner against a fixed vector (eq. (2.1))
-- statement:
--   Let $f_1, f_2, \dots$ be real-valued loss functions on a set $E$ and let $w_1, w_2, \dots \in E$ be the predictions of an online learner, one per round. The **regret** of the learner after $T$ rounds with respect to a competing vector $u$ is
--
--   $$
--   \mathrm{Regret}_T(u) = \sum_{t=1}^{T} f_t(w_t) - \sum_{t=1}^{T} f_t(u).
--   $$
--
--   It is the excess cumulative loss of the learner over the loss of the fixed vector $u$. Regret bounds for Follow-the-Regularized-Leader are stated with this quantity.
--
--   **Formalization Note** Rounds are numbered from $1$; $f_0$ and $w_0$ do not enter. At $T = 0$ the regret is $0$. No structure is assumed on $E$.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 119, eq. (2.1)

import Mathlib

namespace OnlineLearningOCO.FoReL

/-- Regret (Shalev-Shwartz, *Online Learning and Online Convex Optimization*, FnT ML 4(2) (2011),
§2, eq. (2.1), p. 119): the regret of the predictions `w` on the losses `f` after `T` rounds,
with respect to the competing vector `u`,
`Regret_T(u) = ∑_{t=1}^T f_t(w_t) − ∑_{t=1}^T f_t(u)`.
Rounds are 1-based; `f 0` and `w 0` do not enter. -/
def regret {E : Type*} (f : ℕ → E → ℝ) (w : ℕ → E) (T : ℕ) (u : E) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, f t (w t) - ∑ t ∈ Finset.Icc 1 T, f t u

end OnlineLearningOCO.FoReL


