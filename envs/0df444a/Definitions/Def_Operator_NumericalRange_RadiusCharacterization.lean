-- Prove2me | Definitions.Def_Operator_NumericalRange_RadiusCharacterization
-- name    : Operator_NumericalRange_RadiusCharacterization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:22:49.106182+00:00
-- url     : https://prove2.me/theorems/a47bf8a4-de90-4b4b-9dde-88d5e5e88135
-- title:
--   Radius Characterization
-- statement:
--   Definitions and structural lemmas for Radius Characterization, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusCharacterization.lean

import Definitions.Def_Operator_NumericalRange_Radius
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


