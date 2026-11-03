-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_Policy
-- name    : EnvelopeMSLP_MSLP_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:02.99858+00:00
-- url     : https://prove2.me/theorems/ec613333-70d5-4c98-98b4-a270bad783cb
-- title:
--   Decision process of (7)
-- statement:
--   A decision process assigns to each stage $t$ and scenario $\omega$ a decision $x_t(\omega)$ of the stage's dimension.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (7), p.11

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP

namespace EnvelopeMSLP

/-- **Decision process:** `x t ω ∈ ℝ^{n t.succ}` for every stage and scenario. Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (7),
p.11. -/
abbrev MSLP.Policy {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) : Type _ :=
  (t : Fin T) → Ω → Fin (P.n t.succ) → ℝ

end EnvelopeMSLP


