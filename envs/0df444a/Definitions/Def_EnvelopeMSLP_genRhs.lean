-- Prove2me | Definitions.Def_EnvelopeMSLP_genRhs
-- name    : EnvelopeMSLP_genRhs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:28.919731+00:00
-- url     : https://prove2.me/theorems/2edd8fae-b984-43c9-a036-cd2fb88306ce
-- title:
--   The generic right-hand side
-- statement:
--   The vector of polynomial variables of the right-hand-side block of the stacked data.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (5), p.9

import Mathlib
import Definitions.Def_EnvelopeMSLP_LPIndex
open Matrix

namespace EnvelopeMSLP

/-- **The generic right-hand side:** the polynomial variables of the `b` block of `LPIndex m n`. -/
noncomputable def genRhs (m n : ℕ) : Fin m → MvPolynomial (LPIndex m n) ℝ :=
  fun i => MvPolynomial.X (Sum.inr (Sum.inl i))

end EnvelopeMSLP


