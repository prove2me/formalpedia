-- Prove2me | Definitions.Def_Operator_NumericalRange_Bounded
-- name    : Operator_NumericalRange_Bounded
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:30:34.077884+00:00
-- url     : https://prove2.me/theorems/bd0bde69-4bf8-5902-8209-5719bbf09d4e
-- title:
--   Bounded
-- statement:
--   Definitions and structural lemmas for Bounded, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Bounded.lean

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
noncomputable def numericalRadius (A : E →L[ℂ] E) : ℝ :=
  ⨆ z ∈ numericalRange A, ‖z‖


