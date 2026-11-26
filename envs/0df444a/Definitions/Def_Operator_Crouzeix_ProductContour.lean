-- Prove2me | Definitions.Def_Operator_Crouzeix_ProductContour
-- name    : Operator_Crouzeix_ProductContour
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:40:11.708046+00:00
-- url     : https://prove2.me/theorems/a4bb751d-ff71-4a12-b709-d853b93b50f3
-- title:
--   Product Contour
-- statement:
--   Definitions and structural lemmas for Product Contour, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
noncomputable def crouzeixProductRemainderPolynomial
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range p.natDegree,
    Polynomial.monomial i
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        contourIntegral
          (fun z => star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam)


