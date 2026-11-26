-- Prove2me | Definitions.Def_Operator_NumericalRange_Compression
-- name    : Operator_NumericalRange_Compression
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:21:17.86811+00:00
-- url     : https://prove2.me/theorems/cea17214-c86b-5e59-ab48-76fbb8cd7bbe
-- title:
--   Compression
-- statement:
--   Definitions and structural lemmas for Compression, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compression.lean

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]


