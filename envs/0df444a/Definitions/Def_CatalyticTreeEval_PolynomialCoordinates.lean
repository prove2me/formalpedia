-- Prove2me | Definitions.Def_CatalyticTreeEval_PolynomialCoordinates
-- name    : CatalyticTreeEval_PolynomialCoordinates
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T01:32:41.996303+00:00
-- url     : https://prove2.me/theorems/366854e9-b5e2-40bd-bc1c-0ec38c555ce3
-- title:
--   Ordered coefficient and evaluation coordinates for polynomial matching
-- statement:
--   Given an ordered list of monomials, coefficient coordinates record a polynomial coefficient at each listed monomial, and evaluation coordinates record the value of that monomial at a point. Both vectors have dimension exactly the list length. A support-covering list allows their inner product to recover polynomial evaluation.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Lemma B.4.

import Definitions.Def_CatalyticTreeEval_Main_Polynomials

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- The value of one monomial at a point, with a product over all variables. -/
noncomputable def monomialValue {m H : ℕ} (x : Vec m H) (v : Monomial H) : ZMod m :=
  ∏ j, x j ^ v j

/-- Coefficients in a supplied ordered list of monomials; absent coefficients are zero. -/
noncomputable def coefficientCoordinates {m H : ℕ} (f : Poly m H) (ms : List (Monomial H)) :
    Vec m ms.length := fun j => MvPolynomial.coeff (ms.get j) f

/-- Evaluation coordinates in the same supplied order as the coefficient coordinates. -/
noncomputable def evaluationCoordinates {m H : ℕ} (x : Vec m H) (ms : List (Monomial H)) :
    Vec m ms.length := fun j => monomialValue x (ms.get j)

end CatalyticTreeEval.Main


