-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
-- name    : Operator_Crouzeix_ScalarCauchyKernelConstancy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:39:39.831818+00:00
-- url     : https://prove2.me/theorems/2c5c51fe-9a79-4966-926f-cec1532db46e
-- title:
--   Scalar Cauchy Kernel Constancy
-- statement:
--   Definitions and structural lemmas for Scalar Cauchy Kernel Constancy, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelConstancy.lean

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
set_option autoImplicit false
open Complex Set
open scoped Interval Real


