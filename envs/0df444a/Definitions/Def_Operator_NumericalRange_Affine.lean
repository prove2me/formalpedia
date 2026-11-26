-- Prove2me | Definitions.Def_Operator_NumericalRange_Affine
-- name    : Operator_NumericalRange_Affine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:10:44.342374+00:00
-- url     : https://prove2.me/theorems/4858409f-9be7-43a7-87ec-d707457ae488
-- title:
--   Affine
-- statement:
--   Definitions and structural lemmas for Affine, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Affine.lean

import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_Operator_NumericalRange_Helpers
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


