-- Prove2me | Definitions.Def_Operator_Crouzeix_PositiveIntegral
-- name    : Operator_Crouzeix_PositiveIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:34:37.406721+00:00
-- url     : https://prove2.me/theorems/af650ee0-b417-5dfc-bf21-b17a2ddec37f
-- title:
--   Positive Integral
-- statement:
--   Definitions and structural lemmas for Positive Integral, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveIntegral.lean

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
universe u v
namespace ContinuousLinearMap
variable {X : Type u} {E : Type v} [MeasurableSpace X] {μ : Measure X}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
end ContinuousLinearMap


