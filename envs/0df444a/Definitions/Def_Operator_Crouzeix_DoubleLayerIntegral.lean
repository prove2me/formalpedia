-- Prove2me | Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
-- name    : Operator_Crouzeix_DoubleLayerIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:34:23.953685+00:00
-- url     : https://prove2.me/theorems/8ff59239-1662-50a1-815b-0129a59272e4
-- title:
--   Double Layer Integral
-- statement:
--   Definitions and structural lemmas for Double Layer Integral, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayerIntegral.lean

import Definitions.Def_Operator_Crouzeix_AdjointIntegral
import Mathlib.Algebra.Algebra.Spectrum.Basic
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
namespace ContinuousLinearMap
end ContinuousLinearMap


