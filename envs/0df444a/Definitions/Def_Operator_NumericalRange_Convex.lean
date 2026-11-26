-- Prove2me | Definitions.Def_Operator_NumericalRange_Convex
-- name    : Operator_NumericalRange_Convex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:48:52.210794+00:00
-- url     : https://prove2.me/theorems/5b3d9711-63a7-5b02-84b5-c9495f069674
-- title:
--   Convex
-- statement:
--   Definitions and structural lemmas for Convex, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Convex.lean

import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Helpers
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
noncomputable def phaseScalar (p q : ℂ) : ℂ :=
  if p - starRingEnd ℂ q = 0 then 1 else (p - starRingEnd ℂ q)⁻¹


