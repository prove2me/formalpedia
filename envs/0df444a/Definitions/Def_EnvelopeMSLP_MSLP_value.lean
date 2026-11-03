-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_value
-- name    : EnvelopeMSLP_MSLP_value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:28:57.56527+00:00
-- url     : https://prove2.me/theorems/4e98b6c8-56fe-454a-83a5-6f74cec9784f
-- title:
--   Optimal value of (7)
-- statement:
--   The value $V(\theta)$ (the paper's $V_0$) is the supremum of the objective over feasible policies, in the extended reals: $-\infty$ when infeasible and $+\infty$ when unbounded.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (7), p.11

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_IsFeasible
import Definitions.Def_EnvelopeMSLP_MSLP_objective

namespace EnvelopeMSLP

/-- **Optimal value of (7).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (7), p.11: the supremum of the objective over feasible
policies, in `EReal`, so `⊥` when infeasible and `⊤` when unbounded. -/
noncomputable def MSLP.value {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) : EReal :=
  sSup ((fun x => ((P.objective θ x : ℝ) : EReal)) '' {x | P.IsFeasible θ x})

end EnvelopeMSLP


