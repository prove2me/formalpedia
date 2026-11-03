-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_Multiplier
-- name    : EnvelopeMSLP_MSLP_Multiplier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:27.477408+00:00
-- url     : https://prove2.me/theorems/9820f667-91b1-4679-a260-fac26b729107
-- title:
--   Multiplier process of (7)
-- statement:
--   A multiplier process assigns to each stage $t$ and scenario $\omega$ a vector $\lambda_t(\omega)$ with one entry per constraint of stage $t$.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), Theorem 3, p.13

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP

namespace EnvelopeMSLP

/-- **Multiplier process:** `lam t ω ∈ ℝ^{m t}` for every stage and scenario; the object `λ*_t(θ, ξ^t)`
of Theorem 3, Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), p.13. -/
abbrev MSLP.Multiplier {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) : Type _ :=
  (t : Fin T) → Ω → Fin (P.m t) → ℝ

end EnvelopeMSLP


