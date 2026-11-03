-- Prove2me | Definitions.Def_EnvelopeMSLP_reducedPoly
-- name    : EnvelopeMSLP_reducedPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:29.999112+00:00
-- url     : https://prove2.me/theorems/58d00cbd-8b99-4bcf-9a70-37d6c689fdc7
-- title:
--   The polynomials of the third set of (5)
-- statement:
--   For a basis $\beta$, the entries of the vector
--   $$c_\beta\operatorname{adj}(D_\beta)D-c\det(D_\beta),$$
--   polynomials in the data. Their nonnegativity is the third set of display (5).
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (5), p.9

import Mathlib
import Definitions.Def_EnvelopeMSLP_genMatrix
import Definitions.Def_EnvelopeMSLP_genCost
import Definitions.Def_EnvelopeMSLP_detPoly
open Matrix

namespace EnvelopeMSLP

/-- **The polynomials of the third set of display (5).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (5), p.9: the `j`-th entry of
`c_β adj(D_β) D − c det(D_β)`. -/
noncomputable def reducedPoly {m n : ℕ} (β : Fin m ↪ Fin n) (j : Fin n) :
    MvPolynomial (LPIndex m n) ℝ :=
  ((((genCost m n) ∘ β) ᵥ* ((genMatrix m n).submatrix id β).adjugate) ᵥ* genMatrix m n) j -
    detPoly β * genCost m n j

end EnvelopeMSLP


