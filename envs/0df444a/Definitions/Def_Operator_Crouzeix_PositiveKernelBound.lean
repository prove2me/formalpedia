-- Prove2me | Definitions.Def_Operator_Crouzeix_PositiveKernelBound
-- name    : Operator_Crouzeix_PositiveKernelBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:41:54.336383+00:00
-- url     : https://prove2.me/theorems/ad10fd18-5f25-51f4-b6fa-8feec01398f4
-- title:
--   Positive Kernel Bound
-- statement:
--   Definitions and structural lemmas for Positive Kernel Bound, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option autoImplicit false
open ContinuousLinearMap MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


