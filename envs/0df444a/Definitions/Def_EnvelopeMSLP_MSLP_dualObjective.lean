-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_dualObjective
-- name    : EnvelopeMSLP_MSLP_dualObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:45.058632+00:00
-- url     : https://prove2.me/theorems/b18a7ab4-9251-45b0-86dd-ca0eaf26426b
-- title:
--   Dual objective of (7)
-- statement:
--   The objective of the dual of the deterministic equivalent:
--   $$\mathbb E\Big[\sum_{t=1}^T\langle\lambda_t,h_t\rangle-\langle\lambda_1,T_1x_0\rangle\Big].$$
--
--   **Formalization Note** It is written with the sequence of the zero policy started at $x_0$, whose previous decision is $x_0$ at the first stage and $0$ after that.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), §3.1, p.14

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_Multiplier
import Definitions.Def_EnvelopeMSLP_MSLP_path
open Matrix

namespace EnvelopeMSLP

/-- **Dual objective of (7).** The objective of the dual of the deterministic equivalent of Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), §3.1,
p.14: `E[Σ_t ⟨λ_t, h_t⟩ − ⟨λ_1, T_1 x₀⟩]`.

**Formalization Note.** It is written `E[Σ_t ⟨λ_t, h_t − T_t z_{t−1}⟩]`, where `z` is the zero policy
started at `x₀`, so that `z_{t−1}` is `x₀` at the first stage and `0` afterwards. -/
noncomputable def MSLP.dualObjective {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) (lam : P.Multiplier) : ℝ :=
  ∑ ω, P.p ω * ∑ t : Fin T,
    lam t ω ⬝ᵥ (P.h t θ (P.ξ t ω) - P.Tmat t θ (P.ξ t ω) *ᵥ P.path P.x0 0 ω t.castSucc)

end EnvelopeMSLP


