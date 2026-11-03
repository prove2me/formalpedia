-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_IsOptimalMultiplier
-- name    : EnvelopeMSLP_MSLP_IsOptimalMultiplier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:29:23.97625+00:00
-- url     : https://prove2.me/theorems/9d5d075a-eeb5-4fd8-80dc-b8d69afbfd78
-- title:
--   Optimal joint multiplier of (7)
-- statement:
--   A multiplier process is optimal at $\theta$ when it is dual feasible and minimizes the dual objective among dual feasible processes. These are the $\lambda^*$ of (9) in the sense of p.14, where all primal and dual solutions come from one monolithic linear program. An optimal dual of one stage problem (8) is not meant: with those, (9) fails.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), Theorem 3, p.13; §3.1, p.14

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_IsDualFeasible
import Definitions.Def_EnvelopeMSLP_MSLP_dualObjective

namespace EnvelopeMSLP

/-- **Optimal joint multiplier at `θ`:** the object `λ*` of (9), Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), Theorem 3, p.13, read as in §3.1,
p.14 ("all primal and dual solutions for all possible scenarios are known"): dual feasible, and minimal
for the dual objective among dual feasible multipliers. -/
def MSLP.IsOptimalMultiplier {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) (lam : P.Multiplier) : Prop :=
  P.IsDualFeasible θ lam ∧ ∀ mu, P.IsDualFeasible θ mu → P.dualObjective θ lam ≤ P.dualObjective θ mu

end EnvelopeMSLP


