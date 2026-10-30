-- Prove2me | Definitions.Def_GarberOLO_Alg3_alg3Input
-- name    : GarberOLO_Alg3_alg3Input
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:58:48.471899+00:00
-- url     : https://prove2.me/theorems/7a52c888-be4f-438c-bd36-48ac978ee24a
-- title:
--   The point $y_{t+1}$ projected in round $t$ of Algorithm 3
-- statement:
--   In round $t \ge 1$ of Algorithm 3,
--   $$y_{t+1} = \tilde y_t - \eta f_t \ \ (\alpha \ge 1), \qquad y_{t+1} = \tilde y_t + \eta f_t \ \ (\alpha < 1),$$
--   a gradient step for losses and an ascent step for payoffs.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Algorithm 3, line 7, p. 14

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_alg3Y

namespace GarberOLO.Alg3

/-- **The point y_{t+1} that Algorithm 3 projects in round t.**
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Algorithm 3, line 7, p. 14: "y_{t+1} ← ỹ_t − ηf_t if α ≥ 1; ỹ_t + ηf_t if α < 1".

`alg3Input S OK sel c s₁ η ε f t` is y_{t+1}, for rounds `t ≥ 1`. -/
noncomputable def alg3Input {d : ℕ} (S : Setting d)
    (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (sel : (N : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin N → EuclideanSpace ℝ (Fin d)) → Fin N → ℝ)
    (c : ℝ) (s₁ : EuclideanSpace ℝ (Fin d)) (η ε : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  if 1 ≤ S.α then alg3Y S OK sel c s₁ η ε f t - η • f t
  else alg3Y S OK sel c s₁ η ε f t + η • f t

end GarberOLO.Alg3


