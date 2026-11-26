-- Prove2me | Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
-- name    : Operator_Crouzeix_GeneralSymmetrized
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:46:20.746859+00:00
-- url     : https://prove2.me/theorems/4f449ba1-f778-4a49-9773-bcb578684b69
-- title:
--   General Symmetrized
-- statement:
--   Definitions and structural lemmas for General Symmetrized, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace SmoothJordanDomain
end SmoothJordanDomain


