-- Prove2me | Definitions.Def_Operator_NumericalRange_RadiusAlgebra
-- name    : Operator_NumericalRange_RadiusAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:22:20.463522+00:00
-- url     : https://prove2.me/theorems/6fb01e38-7332-5c53-a8d9-4bee72aaa952
-- title:
--   Radius Algebra
-- statement:
--   Definitions and structural lemmas for Radius Algebra, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAlgebra.lean

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


