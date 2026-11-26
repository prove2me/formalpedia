-- Prove2me | Definitions.Def_Operator_NumericalRange_Helpers
-- name    : Operator_NumericalRange_Helpers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:31:37.088801+00:00
-- url     : https://prove2.me/theorems/15f748e4-b31d-422b-80f0-1365eb5bcbd1
-- title:
--   Helpers
-- statement:
--   Definitions and structural lemmas for Helpers, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Helpers.lean

import Definitions.Def_Operator_NumericalRange_Basic
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


