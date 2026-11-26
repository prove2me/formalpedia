-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
-- name    : Operator_Crouzeix_ScalarCauchyKernelWinding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:40:09.710149+00:00
-- url     : https://prove2.me/theorems/bfeffc41-1d0f-40c9-a4ec-748562449160
-- title:
--   Scalar Cauchy Kernel Winding
-- statement:
--   Definitions and structural lemmas for Scalar Cauchy Kernel Winding, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelWinding.lean

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real


