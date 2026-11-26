-- Prove2me | Definitions.Def_Operator_Crouzeix_AuxOperator
-- name    : Operator_Crouzeix_AuxOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:33:13.885344+00:00
-- url     : https://prove2.me/theorems/77fd5d38-071d-5930-8ae9-354c9a79af25
-- title:
--   Aux Operator
-- statement:
--   Definitions and structural lemmas for Aux Operator, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace SmoothJordanDomain
end SmoothJordanDomain
noncomputable def crouzeixAuxiliaryOperator (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (h : ℂ → ℂ) : E →L[ℂ] E :=
  (2 * (Real.pi : ℂ) * I)⁻¹ •
    contourIntegral (fun z => h z • resolvent A z) Omega.boundaryParam
noncomputable def crouzeixPolynomialAuxiliaryOperator (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : E →L[ℂ] E :=
  crouzeixAuxiliaryOperator A Omega (fun z => star (Polynomial.eval z p))


