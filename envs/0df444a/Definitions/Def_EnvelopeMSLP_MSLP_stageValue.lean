-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_stageValue
-- name    : EnvelopeMSLP_MSLP_stageValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:29:47.395678+00:00
-- url     : https://prove2.me/theorems/623bb45a-78e8-4c44-ae10-7b12c3327799
-- title:
--   Stage value functions (8)
-- statement:
--   The stage value at the node of $\omega$:
--   $$V_t(x_{t-1},\xi_t,\theta)=\max_{x_t}\ \langle c_t(\theta),x_t\rangle+\mathbb E[V_{t+1}(x_t,\xi_{t+1},\theta)\mid\xi^t]\quad\text{s.t. }W_t(\theta)x_t+T_t(\theta)x_{t-1}\le h_t(\theta).$$
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (8), p.12

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_postValue

namespace EnvelopeMSLP

/-- **Stage value functions (8).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (8), p.12: `V_t(x_{t−1}, ξ_t, θ) = max ⟨c_t, x_t⟩ +
E[V_{t+1}(x_t, ξ_{t+1}, θ) | ξ^t]` s.t. `W_t x_t + T_t x_{t−1} ≤ h_t`, at the node of `ω`. -/
noncomputable def MSLP.stageValue {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) (t : Fin T) (x : Fin (P.n t.castSucc) → ℝ) (ω : Ω) :
    EReal :=
  P.stageStep θ t (P.postValue θ t.succ) x ω

end EnvelopeMSLP


