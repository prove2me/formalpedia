-- Prove2me | Definitions.Def_Operator_NumericalRange_Compact
-- name    : Operator_NumericalRange_Compact
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:20:38.35568+00:00
-- url     : https://prove2.me/theorems/c001cbe6-aa97-515d-9bf8-9c39d4972921
-- title:
--   Compact
-- statement:
--   Definitions and structural lemmas for Compact, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compact.lean

import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Operator_NumericalRange_Basic
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


