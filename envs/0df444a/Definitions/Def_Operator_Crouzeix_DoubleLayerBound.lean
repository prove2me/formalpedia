-- Prove2me | Definitions.Def_Operator_Crouzeix_DoubleLayerBound
-- name    : Operator_Crouzeix_DoubleLayerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:43:12.207415+00:00
-- url     : https://prove2.me/theorems/6c604307-fa52-47b9-a34e-25ca64a7e264
-- title:
--   Double Layer Bound
-- statement:
--   Definitions and structural lemmas for Double Layer Bound, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayerBound.lean

import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveKernelBound
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


