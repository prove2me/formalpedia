-- Prove2me | Definitions.Def_Operator_Crouzeix_CircleKernel
-- name    : Operator_Crouzeix_CircleKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:55:16.661868+00:00
-- url     : https://prove2.me/theorems/b2685f25-4047-4980-b819-8a69dfa7b303
-- title:
--   Circle Kernel
-- statement:
--   Definitions and structural lemmas for Circle Kernel, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleKernel.lean

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


