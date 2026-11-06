-- Prove2me | Definitions.Def_IAFTRL_Run_gEst
-- name    : IAFTRL_Run_gEst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:48:35.460684+00:00
-- url     : https://prove2.me/theorems/987aa30f-f4b4-4d2a-9bd9-f7ceb420a6ce
-- title:
--   Estimated loss differences $g_{t,a}$
-- statement:
--   In round $t$ the **estimated loss difference** of action $a$ relative to the reference action is
--   $$
--   g_{t,a}=(a-r_t)^\top v_{t,A_t}\,Y_t ,
--   $$
--   where $r_t$ is the reference action computed from $\sum_{s<t}\hat\theta_s$ and $v_{t,A_t}=M(p_t)^{-1}A_t$. It is the increment of $\hat L_{a}-\hat L_{r_t}$ in round $t$.
--
--   **Formalization Note** 0-based rounds.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Lemma D.15, p.88; Lemma D.4, p.70

import Mathlib
import Definitions.Def_IAFTRL_Run_cumEst
import Definitions.Def_IAFTRL_refArm

namespace IAFTRL

open Matrix

/-- **The estimated loss differences `g_{t,a}`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma D.15, p.88: "For IA-FTRL, define
`g_{t,a} = (a − r_t)^⊤ v_{t,A_t} Y_t`"; also Lemma D.4, p.70.

`R.gEst arms t a ω = (a − r_t)^⊤ M(p_t)^{-1} a_{A_t} · Y_t` with `r_t = refArm arms (Σ_{s<t} θ̂_s)`
(0-based round `t`). -/
noncomputable def Run.gEst {d K : ℕ} {Ω : Type*} (R : Run d K Ω)
    (arms : Fin K → Fin d → ℝ) (t : ℕ) (a : Fin K) (ω : Ω) : ℝ :=
  ((arms a - refArm arms (R.cumEst arms t ω)) ⬝ᵥ vCoef arms (R.p t ω) (R.A t ω)) * R.Y t ω

end IAFTRL


