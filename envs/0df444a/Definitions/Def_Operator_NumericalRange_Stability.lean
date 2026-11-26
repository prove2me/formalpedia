-- Prove2me | Definitions.Def_Operator_NumericalRange_Stability
-- name    : Operator_NumericalRange_Stability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:24:30.342868+00:00
-- url     : https://prove2.me/theorems/bae04136-9e43-4e86-8a37-f4c39cc1d4c3
-- title:
--   Stability
-- statement:
--   Definitions and structural lemmas for Stability, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Stability.lean

import Definitions.Def_Operator_NumericalRange_Bounded
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


