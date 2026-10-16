-- Prove2me | Definitions.Def_EngagementOpt_Survey_condUtility
-- name    : EngagementOpt_Survey_condUtility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:20:20.387694+00:00
-- url     : https://prove2.me/theorems/853f0293-8982-4aa8-b36d-8280a109f751
-- title:
--   (8): system 2's expected utility given the session length, $\mathbb E[S\mid T=t]$
-- statement:
--   Each item that system 2 enjoys gives it value of mean $\bar v$, and every step on the platform costs it the outside option $W$. Its expected utility given that the session lasts $t$ steps is defined, as in equation (8) of the paper, by
--
--   $$
--   \mathbb E[S\mid T=t]=\bar v\cdot\mathbb E[T_q\mid T=t]-Wt,
--   $$
--
--   where $\mathbb E[T_q\mid T=t]$ is the conditional mean (9) (`condMeanTq`).
--
--   This is the quantity whose dependence on $t$ Theorem 5.1 characterizes.
--
--   **Formalization Note** Equation (8) is a modelling identity in the paper (it uses that the values $v_t$ are i.i.d. with mean $\bar v$ and independent of the phase lengths); here it is taken as the definition of $\mathbb E[S\mid T=t]$.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 19, eq. (8)

import Mathlib
import Definitions.Def_EngagementOpt_Survey_condMeanTq

namespace EngagementOpt.Survey

/-- Equation (8) of arXiv:2202.11776v3, p. 19, taken as the definition of system 2's expected
utility given the session length: `E[S | T = t] = v̄ · E[T_q | T = t] - W t`, where `v̄` is the
mean value of an item and `W` the per-step outside option. -/
noncomputable def condUtility (v W p q : ℝ) (t : ℕ) : ℝ :=
  v * condMeanTq p q t - W * t

end EngagementOpt.Survey


