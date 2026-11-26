-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
-- name    : Operator_Crouzeix_SmoothJordanCauchyFormula
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:41:06.596799+00:00
-- url     : https://prove2.me/theorems/a00ecdbf-39e8-498e-be0c-027006da9746
-- title:
--   Smooth Jordan Cauchy Formula
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Cauchy Formula, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology


