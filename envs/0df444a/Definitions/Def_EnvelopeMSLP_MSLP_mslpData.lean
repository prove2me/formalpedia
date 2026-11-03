-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_mslpData
-- name    : EnvelopeMSLP_MSLP_mslpData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:17.769618+00:00
-- url     : https://prove2.me/theorems/9dbfe187-8824-4f90-8044-a9db59ff9857
-- title:
--   The joint data vector of (7)
-- statement:
--   The point of $\mathbb R^\iota$ listing every entry of $\mathcal D_t(\theta,\xi_t(\omega))=(W_t,T_t,c_t,h_t)(\theta,\xi_t(\omega))$, for all $t$ and $\omega$. A polynomial in this vector may mix stages and scenarios, as the deterministic equivalent does.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), p.11; §3.1, p.14

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_DataIndex

namespace EnvelopeMSLP

/-- **The joint data vector of (7) at `θ`:** all entries of `D_t(θ, ξ_t(ω)) = (W_t, T_t, c_t, h_t)`, for all
`t`, `ω`. Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), p.11. A polynomial in this vector may mix stages and scenarios, as the deterministic
equivalent does. -/
def MSLP.mslpData {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) : P.DataIndex → ℝ
  | ⟨t, ω, Sum.inl ij⟩ => P.W t θ (P.ξ t ω) ij.1 ij.2
  | ⟨t, ω, Sum.inr (Sum.inl ij)⟩ => P.Tmat t θ (P.ξ t ω) ij.1 ij.2
  | ⟨t, ω, Sum.inr (Sum.inr (Sum.inl j))⟩ => P.c t θ (P.ξ t ω) j
  | ⟨t, ω, Sum.inr (Sum.inr (Sum.inr i))⟩ => P.h t θ (P.ξ t ω) i

end EnvelopeMSLP


