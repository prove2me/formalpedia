-- Prove2me | Definitions.Def_Operator_Crouzeix_AdjointIntegral
-- name    : Operator_Crouzeix_AdjointIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:33:36.128587+00:00
-- url     : https://prove2.me/theorems/4ab9760d-2d07-54b7-8f71-ca6bb67c5183
-- title:
--   Adjoint Integral
-- statement:
--   Definitions and structural lemmas for Adjoint Integral, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AdjointIntegral.lean

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.InnerProductSpace.Adjoint
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace Interval
universe u v w
namespace ContinuousLinearMap
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}
variable {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
end ContinuousLinearMap


