-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_IsFeasible
-- name    : EnvelopeMSLP_MSLP_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:28:07.663181+00:00
-- url     : https://prove2.me/theorems/7ea343bf-d37b-44ce-87b2-86d45183a395
-- title:
--   Feasible policy of (7)
-- statement:
--   A policy $x$ is feasible at $\theta$ when it is nonanticipative and for all $t$ and $\omega$,
--   $$W_t(\theta,\xi_t)x_t+T_t(\theta,\xi_t)x_{t-1}\le h_t(\theta,\xi_t),$$
--   with $x_0$ the given vector.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (7), p.11

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_IsNonanticipative
import Definitions.Def_EnvelopeMSLP_MSLP_path
open Matrix

namespace EnvelopeMSLP

/-- **Feasible policy of (7) at `θ`.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (7), p.11: `x` is nonanticipative and, for every
stage and scenario, `W_t x_t + T_t x_{t−1} ≤ h_t`, with the data at `(θ, ξ_t(ω))` and `x_0` given. -/
def MSLP.IsFeasible {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) (x : P.Policy) : Prop :=
  P.IsNonanticipative x ∧ ∀ (t : Fin T) (ω : Ω),
    P.W t θ (P.ξ t ω) *ᵥ x t ω + P.Tmat t θ (P.ξ t ω) *ᵥ P.path P.x0 x ω t.castSucc ≤
      P.h t θ (P.ξ t ω)

end EnvelopeMSLP


