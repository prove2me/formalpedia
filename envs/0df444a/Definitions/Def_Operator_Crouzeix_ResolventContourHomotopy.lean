-- Prove2me | Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
-- name    : Operator_Crouzeix_ResolventContourHomotopy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:41:31.213801+00:00
-- url     : https://prove2.me/theorems/ff7bd16b-0dc1-5d82-91c6-81538af57a80
-- title:
--   Resolvent Contour Homotopy
-- statement:
--   Definitions and structural lemmas for Resolvent Contour Homotopy, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


