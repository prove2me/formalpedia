-- Prove2me | Definitions.Def_Operator_NumericalRange_RadiusFiniteDimensional
-- name    : Operator_NumericalRange_RadiusFiniteDimensional
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:24:03.136611+00:00
-- url     : https://prove2.me/theorems/19570ab8-bdda-46b8-9b92-5a4644df148c
-- title:
--   Radius Finite Dimensional
-- statement:
--   Definitions and structural lemmas for Radius Finite Dimensional, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusFiniteDimensional.lean

import Definitions.Def_Operator_NumericalRange_Compact
import Definitions.Def_Operator_NumericalRange_Radius
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Nontrivial E]


