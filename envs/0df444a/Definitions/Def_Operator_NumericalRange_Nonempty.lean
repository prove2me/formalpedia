-- Prove2me | Definitions.Def_Operator_NumericalRange_Nonempty
-- name    : Operator_NumericalRange_Nonempty
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:14:30.735437+00:00
-- url     : https://prove2.me/theorems/adbc6537-18df-43f0-9658-d4a080f18ee5
-- title:
--   Nonempty
-- statement:
--   Definitions and structural lemmas for Nonempty, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Nonempty.lean

import Mathlib.Analysis.Normed.Module.Normalize
import Definitions.Def_Operator_NumericalRange_Basic
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


