-- Prove2me | Definitions.Def_IAFTRL_Run_thetaHat
-- name    : IAFTRL_Run_thetaHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:33.709583+00:00
-- url     : https://prove2.me/theorems/a0c20501-7724-46ce-93ef-a9c05d8fa6d3
-- title:
--   Least-squares estimate $\hat\theta_t$
-- statement:
--   In round $t$ the learner forms the **least-squares estimate** of the loss vector
--   $$
--   \hat\theta_t=v_{t,A_t}\,Y_t=M(p_t)^{-1}A_t\,Y_t ,
--   $$
--   from the played action $A_t$, the feedback $Y_t$ and its sampling distribution $p_t$ (Algorithm 1, line 7). The estimated loss of action $a$ is $\hat\ell_{t,a}=a^\top\hat\theta_t$.
--
--   **Formalization Note** 0-based rounds.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Algorithm 1, line 7, p.18; Section 2.1, p.17

import Mathlib
import Definitions.Def_IAFTRL_Run
import Definitions.Def_IAFTRL_vCoef

namespace IAFTRL

/-- **The least-squares estimate `θ̂_t`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Algorithm 1, line 7, p.18: "Set `θ̂_t = v_{t,A_t}Y_t`",
with `v_{t,a} = v_a(p_t) = M(p_t)^{-1}a` (p.17).

`R.thetaHat arms t ω = Y_t · M(p_t)^{-1} a_{A_t}` (0-based round `t`). -/
noncomputable def Run.thetaHat {d K : ℕ} {Ω : Type*} (R : Run d K Ω)
    (arms : Fin K → Fin d → ℝ) (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  R.Y t ω • vCoef arms (R.p t ω) (R.A t ω)

end IAFTRL


