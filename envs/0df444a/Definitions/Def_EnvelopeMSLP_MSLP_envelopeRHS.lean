-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_envelopeRHS
-- name    : EnvelopeMSLP_MSLP_envelopeRHS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:28:05.129758+00:00
-- url     : https://prove2.me/theorems/d020b218-1163-4e45-85b2-3ee85aecefc1
-- title:
--   The right-hand side of (9)
-- statement:
--   For a policy $x$ and multipliers $\lambda$,
--   $$\mathbb E\Big[\sum_{t=1}^T\langle\nabla c_t(\theta),x_t\rangle+\Big\langle\lambda_t,\nabla h_t(\theta)-\tfrac{d}{d\theta}T_t(\theta)x_{t-1}-\tfrac{d}{d\theta}W_t(\theta)x_t\Big\rangle\Big].$$
--   All derivatives are taken in $\theta$ at the fixed noise value, entrywise, and $x_0$ is the given vector.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (9), p.13

import Mathlib
import Definitions.Def_EnvelopeMSLP_matDeriv
import Definitions.Def_EnvelopeMSLP_MSLP_Policy
import Definitions.Def_EnvelopeMSLP_MSLP_Multiplier
import Definitions.Def_EnvelopeMSLP_MSLP_path
open Matrix

namespace EnvelopeMSLP

/-- **The right-hand side of (9).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (9), p.13:
`E[Σ_t (⟨∇c_t(θ), x_t⟩ + ⟨λ_t, ∇h_t(θ) − d/dθ T_t(θ) x_{t−1} − d/dθ W_t(θ) x_t⟩)]`.

**Formalization Note.** The derivatives are in `θ` at fixed noise `ξ_t(ω)`, taken entrywise. The
first-stage term uses the given `x₀`. -/
noncomputable def MSLP.envelopeRHS {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) (x : P.Policy) (lam : P.Multiplier) : ℝ :=
  ∑ ω, P.p ω * ∑ t : Fin T,
    (deriv (fun θ' => P.c t θ' (P.ξ t ω)) θ ⬝ᵥ x t ω +
      lam t ω ⬝ᵥ (deriv (fun θ' => P.h t θ' (P.ξ t ω)) θ -
        matDeriv (fun θ' => P.Tmat t θ' (P.ξ t ω)) θ *ᵥ P.path P.x0 x ω t.castSucc -
        matDeriv (fun θ' => P.W t θ' (P.ξ t ω)) θ *ᵥ x t ω))

end EnvelopeMSLP


