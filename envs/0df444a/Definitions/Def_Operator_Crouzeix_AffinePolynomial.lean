-- Prove2me | Definitions.Def_Operator_Crouzeix_AffinePolynomial
-- name    : Operator_Crouzeix_AffinePolynomial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:52:39.700619+00:00
-- url     : https://prove2.me/theorems/808bc4bf-b500-5690-b073-4110a9db2950
-- title:
--   Affine Polynomial
-- statement:
--   Definitions and structural lemmas for Affine Polynomial, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffinePolynomial.lean

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Definitions.Def_Operator_SpectralSet_Basic
set_option autoImplicit false
open scoped Polynomial
namespace Polynomial
noncomputable def affineComposition (p : ℂ[X]) (a b : ℂ) : ℂ[X] :=
  p.comp (C a * X + C b)
end Polynomial


