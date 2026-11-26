-- Prove2me | Definitions.Def_Operator_NumericalRange_Basic
-- name    : Operator_NumericalRange_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:29:58.964686+00:00
-- url     : https://prove2.me/theorems/ff9331d6-5406-5f94-9d29-23a37a2d9658
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Basic.lean

import Mathlib.Analysis.InnerProductSpace.Basic
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
noncomputable def numericalRange (A : E →L[ℂ] E) : Set ℂ :=
  { z | ∃ x : E, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z }


