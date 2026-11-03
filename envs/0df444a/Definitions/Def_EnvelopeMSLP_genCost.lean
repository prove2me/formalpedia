-- Prove2me | Definitions.Def_EnvelopeMSLP_genCost
-- name    : EnvelopeMSLP_genCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:35.535292+00:00
-- url     : https://prove2.me/theorems/d86ae28b-b3ca-463e-b423-08c04be3f186
-- title:
--   The generic objective
-- statement:
--   The vector of polynomial variables of the objective block of the stacked data.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (5), p.9

import Mathlib
import Definitions.Def_EnvelopeMSLP_LPIndex
open Matrix

namespace EnvelopeMSLP

/-- **The generic objective:** the polynomial variables of the `c` block of `LPIndex m n`. -/
noncomputable def genCost (m n : ℕ) : Fin n → MvPolynomial (LPIndex m n) ℝ :=
  fun j => MvPolynomial.X (Sum.inr (Sum.inr j))

end EnvelopeMSLP


