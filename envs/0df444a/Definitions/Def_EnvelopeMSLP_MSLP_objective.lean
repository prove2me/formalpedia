-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_objective
-- name    : EnvelopeMSLP_MSLP_objective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:05.645779+00:00
-- url     : https://prove2.me/theorems/0310c9d4-28b8-402b-a92c-ff5e4dec4df1
-- title:
--   Objective of (7)
-- statement:
--   The objective of a policy $x$ at $\theta$ is
--   $$\mathbb E\Big[\sum_{t=1}^T\langle c_t(\theta,\xi_t),x_t\rangle\Big],$$
--   a finite sum over scenarios weighted by their probabilities.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (7), p.11

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_Policy
open Matrix

namespace EnvelopeMSLP

/-- **Objective of (7).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (7), p.11: `E[Σ_t ⟨c_t(θ, ξ_t), x_t⟩]`. -/
noncomputable def MSLP.objective {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) (x : P.Policy) : ℝ :=
  ∑ ω, P.p ω * ∑ t : Fin T, P.c t θ (P.ξ t ω) ⬝ᵥ x t ω

end EnvelopeMSLP


