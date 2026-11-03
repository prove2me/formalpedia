-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_IsNonanticipativeMultiplier
-- name    : EnvelopeMSLP_MSLP_IsNonanticipativeMultiplier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:23.811599+00:00
-- url     : https://prove2.me/theorems/c4edb1a6-1339-453c-94bc-5c598d404473
-- title:
--   Nonanticipative multipliers
-- statement:
--   A multiplier process is nonanticipative when $\lambda_t=\lambda_t(\theta,\xi^t)$ is a function of the history $\xi^t$.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), Theorem 3, p.13

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_Multiplier
import Definitions.Def_EnvelopeMSLP_MSLP_SameHistory

namespace EnvelopeMSLP

/-- **Nonanticipative multipliers:** `λ_t = λ_t(θ, ξ^t)`, Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), Theorem 3, p.13. -/
def MSLP.IsNonanticipativeMultiplier {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (lam : P.Multiplier) : Prop :=
  ∀ (t : Fin T) (ω ω' : Ω), P.SameHistory t.succ ω ω' → lam t ω = lam t ω'

end EnvelopeMSLP


