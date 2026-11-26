-- Prove2me | Definitions.Def_Operator_NumericalRange_Adjoint
-- name    : Operator_NumericalRange_Adjoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:20:10.8218+00:00
-- url     : https://prove2.me/theorems/9d8f33c2-2013-40d1-a5f8-297dfcfcbb0a
-- title:
--   Adjoint
-- statement:
--   Definitions and structural lemmas for Adjoint, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Adjoint.lean

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Definitions.Def_Operator_NumericalRange_Basic
set_option autoImplicit false
open scoped InnerProductSpace
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


