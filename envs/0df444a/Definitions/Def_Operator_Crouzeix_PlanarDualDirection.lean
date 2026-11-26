-- Prove2me | Definitions.Def_Operator_Crouzeix_PlanarDualDirection
-- name    : Operator_Crouzeix_PlanarDualDirection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:04:00.754709+00:00
-- url     : https://prove2.me/theorems/947d571c-06e6-59b5-975a-dd4e1893fd16
-- title:
--   Planar Dual Direction
-- statement:
--   Definitions and structural lemmas for Planar Dual Direction, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PlanarDualDirection.lean

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
set_option autoImplicit false
open Complex
noncomputable def realContinuousLinearMapCoefficient
    (f : ℂ →L[ℝ] ℝ) : ℂ :=
  ⟨f 1, f I⟩


