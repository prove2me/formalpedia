-- Prove2me | Definitions.Def_EnvelopeMSLP_detPoly
-- name    : EnvelopeMSLP_detPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:31.012882+00:00
-- url     : https://prove2.me/theorems/bc0e34f3-6cb7-454c-8f7e-695f507445a9
-- title:
--   The polynomial $\det(D_\beta)$
-- statement:
--   The determinant of the generic basis matrix, a polynomial in the entries of the data.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (5), p.9

import Mathlib
import Definitions.Def_EnvelopeMSLP_genMatrix
open Matrix

namespace EnvelopeMSLP

/-- **The polynomial `det(D_β)`** in the entries of the data. Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (5), p.9. -/
noncomputable def detPoly {m n : ℕ} (β : Fin m ↪ Fin n) : MvPolynomial (LPIndex m n) ℝ :=
  ((genMatrix m n).submatrix id β).det

end EnvelopeMSLP


