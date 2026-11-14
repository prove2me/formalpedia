-- Prove2me | Definitions.Def_CatalyticTreeEval_SubsetPolynomials
-- name    : CatalyticTreeEval_SubsetPolynomials
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T02:15:59.924849+00:00
-- url     : https://prove2.me/theorems/45ee12c1-eafe-4f5b-a5b7-46c1e16c36fa
-- title:
--   Polynomial restriction to a Boolean subset
-- statement:
--   For a subset of the polynomial variables, define its Boolean characteristic point and the polynomial obtained by setting all variables outside the subset to zero. This is the restriction used for the canonical matching-vector construction.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Lemma B.1.

import Definitions.Def_CatalyticTreeEval_Main_Polynomials

set_option autoImplicit false

namespace CatalyticTreeEval.Main

def subsetPoint {H : ℕ} (T : Finset (Fin H)) : Fin H → Bool := fun i => decide (i ∈ T)

/-- Set all variables outside a chosen subset to zero. -/
noncomputable def restrictPolynomial {m H : ℕ} (T : Finset (Fin H))
    (f : Poly m H) : Poly m H :=
  MvPolynomial.rename (fun i : {j // j ∈ T} => i.val)
    (MvPolynomial.killCompl (f := fun i : {j // j ∈ T} => i.val) Subtype.val_injective f)

end CatalyticTreeEval.Main


