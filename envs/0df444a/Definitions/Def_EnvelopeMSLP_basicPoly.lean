-- Prove2me | Definitions.Def_EnvelopeMSLP_basicPoly
-- name    : EnvelopeMSLP_basicPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:33.662201+00:00
-- url     : https://prove2.me/theorems/4912cd60-2373-4a61-8cf1-1e1ecfb0ea09
-- title:
--   The polynomials $P_i$
-- statement:
--   For a basis $\beta$, the polynomials in the data
--   $$P_i(\mathcal D)=\operatorname{adj}(D_\beta)_{(i,:)}\,b,\qquad i=1,\dots,m.$$
--   They give the second set of display (5).
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), proof of Lemma 1, p.9

import Mathlib
import Definitions.Def_EnvelopeMSLP_genMatrix
import Definitions.Def_EnvelopeMSLP_genRhs
open Matrix

namespace EnvelopeMSLP

/-- **The polynomials `P_i(D) = adj(D_β)_(i,:) b`.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), proof of Lemma 1, p.9. -/
noncomputable def basicPoly {m n : ℕ} (β : Fin m ↪ Fin n) (i : Fin m) :
    MvPolynomial (LPIndex m n) ℝ :=
  (((genMatrix m n).submatrix id β).adjugate *ᵥ genRhs m n) i

end EnvelopeMSLP


