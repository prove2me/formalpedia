-- Prove2me | Definitions.Def_CatalyticTreeEval_WeightDetector
-- name    : CatalyticTreeEval_WeightDetector
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T01:40:50.821337+00:00
-- url     : https://prove2.me/theorems/60278e98-9d14-49c3-8baf-b9bdc4a55579
-- title:
--   Prime-power symmetric weight detector construction
-- statement:
--   Finite Boolean monomials, elementary symmetric polynomials and binomial evaluation matrices define the source prime-power weight detector. Its residues determine whether the Boolean weight equals the prescribed residue; degree, symmetry and evaluation properties are separate proved theorems.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Sections 3.1/4 and Appendix B. Native composition adapts the shared-tape halting-redirection construction of tcslib/cslib.

import Definitions.Def_CatalyticTreeEval_Main_Polynomials

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- The finite lower-unitriangular binomial evaluation matrix used in Lemma B.5. -/
def binomialMatrix (p q : ℕ) : Matrix (Fin q) (Fin q) (ZMod p) :=
  fun i j => (i.val.choose j.val : ZMod p)

/-- Binomial-basis interpolation of the target residue indicator. -/
noncomputable def detectorCoefficients (p q w : ℕ) : Fin q → ZMod p :=
  ((binomialMatrix p q)⁻¹).mulVec (fun i => if i.val = w % q then 0 else 1)

/-- Symmetric multilinear weight detector from its elementary-symmetric coefficients. -/
noncomputable def weightDetector (p e w H : ℕ) : Poly p H :=
  ∑ j : Fin (p ^ e), MvPolynomial.C (detectorCoefficients p (p ^ e) w j) *
    MvPolynomial.esymm (Fin H) (ZMod p) j.val

end CatalyticTreeEval.Main


