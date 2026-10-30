-- Prove2me | Definitions.Def_MohriFoML_OnlineToBatch_regret
-- name    : MohriFoML_OnlineToBatch_regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:07:27.894019+00:00
-- url     : https://prove2.me/theorems/e3d71ad8-e317-4cf8-81d5-5bfd49c07b01
-- title:
--   Regret $R_T$ of an on-line algorithm on a sample, (8.25)
-- statement:
--   Let $H$ be a set of hypotheses, $L$ a loss, $A$ an on-line algorithm and $h_1, \dots, h_T$ the hypotheses it generates on the sample $S = ((x_1, y_1), \dots, (x_T, y_T))$. The **regret** of $A$ on $S$ is
--
--   $$
--   R_T = \sum_{t=1}^T L(h_t(x_t), y_t) - \inf_{h \in H} \sum_{t=1}^T L(h(x_t), y_t).
--   $$
--
--   It compares the cumulative loss of the on-line algorithm with that of the best fixed hypothesis of $H$ in hindsight; Theorem 8.15 turns a bound on $R_T / T$ into a bound on the generalization error of the averaged hypothesis.
--
--   **Formalization Note** The book writes $\min_{h \in H}$; for an infinite $H$ the minimum need not be attained, so the infimum is used, which equals the minimum whenever it exists. In every theorem $H$ is nonempty and the losses are nonnegative, so the infimum is that of a nonempty family bounded below.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 202 (PDF p. 219), §8.4, equation (8.25)

import Mathlib
import Definitions.Def_MohriFoML_OnlineToBatch_OnlineAlgorithm
import Definitions.Def_MohriFoML_OnlineToBatch_hypSeq

namespace MohriFoML.OnlineToBatch

/-- **Regret of an on-line algorithm on a sample, (8.25).**
Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018,
§8.4, p. 202 (PDF p. 219), equation (8.25):
`R_T = ∑_{t=1}^T L(h_t(x_t), y_t) − min_{h∈H} ∑_{t=1}^T L(h(x_t), y_t)`.

`regret H L A S` is the cumulative loss of the hypotheses `hypSeq A S t` on the sample
`S : Fin T → X × Y`, minus the infimum over `h ∈ H` of the cumulative loss of `h` on `S`.

**Formalization Note.** The book's `min` is taken as an infimum `⨅ h : H` (equal to the minimum
whenever it is attained; for infinite `H` the minimum need not exist). In the theorems `H` is
nonempty (it contains every hypothesis output by `A`) and the losses are nonnegative, so the
infimum is over a nonempty, bounded-below family and is the genuine infimum, not Lean's junk
value. -/
noncomputable def regret {X Y E : Type*} {T : ℕ} (H : Set (X → E)) (L : E → Y → ℝ)
    (A : OnlineAlgorithm X Y E) (S : Fin T → X × Y) : ℝ :=
  (∑ t : Fin T, L (hypSeq A S t (S t).1) (S t).2) -
    ⨅ h : H, ∑ t : Fin T, L ((h : X → E) (S t).1) (S t).2

end MohriFoML.OnlineToBatch


