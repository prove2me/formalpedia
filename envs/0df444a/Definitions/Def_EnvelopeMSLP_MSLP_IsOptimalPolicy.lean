-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_IsOptimalPolicy
-- name    : EnvelopeMSLP_MSLP_IsOptimalPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:29:16.622591+00:00
-- url     : https://prove2.me/theorems/bf704837-8219-4458-9ad8-db0840adab69
-- title:
--   Optimal policy of (7)
-- statement:
--   A policy is optimal at $\theta$ when it is feasible at $\theta$ and its objective is at least that of every feasible policy.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (7), p.11

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_IsFeasible
import Definitions.Def_EnvelopeMSLP_MSLP_objective

namespace EnvelopeMSLP

/-- **Optimal policy of (7) at `θ`.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (7), p.11: feasible, and the objective of every
feasible policy is at most its objective. -/
def MSLP.IsOptimalPolicy {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) (x : P.Policy) : Prop :=
  P.IsFeasible θ x ∧ ∀ y, P.IsFeasible θ y → P.objective θ y ≤ P.objective θ x

end EnvelopeMSLP


