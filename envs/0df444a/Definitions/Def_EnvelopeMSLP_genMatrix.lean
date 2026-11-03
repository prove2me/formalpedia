-- Prove2me | Definitions.Def_EnvelopeMSLP_genMatrix
-- name    : EnvelopeMSLP_genMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:40.309778+00:00
-- url     : https://prove2.me/theorems/023aa3cc-6eda-4ef8-951f-097671f12d9e
-- title:
--   The generic matrix
-- statement:
--   The $m\times n$ matrix over the polynomial ring $\mathbb R[X_k: k\in\text{LPIndex}]$ whose entries are the variables of the matrix block. It serves to state that the conditions of display (5) are polynomial in the data.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (5), p.9

import Mathlib
import Definitions.Def_EnvelopeMSLP_LPIndex
open Matrix

namespace EnvelopeMSLP

/-- **The generic matrix:** its entries are the polynomial variables of the matrix block of
`LPIndex m n`. Used to state that the conditions of display (5), Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), p.9, are polynomial. -/
noncomputable def genMatrix (m n : ℕ) : Matrix (Fin m) (Fin n) (MvPolynomial (LPIndex m n) ℝ) :=
  Matrix.of fun i j => MvPolynomial.X (Sum.inl (i, j))

end EnvelopeMSLP


