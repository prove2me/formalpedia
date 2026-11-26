-- Prove2me | Definitions.Def_Operator_Crouzeix_VonNeumann
-- name    : Operator_Crouzeix_VonNeumann
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:31:13.800286+00:00
-- url     : https://prove2.me/theorems/0dd68834-8ab4-51c0-8636-857173e02ad6
-- title:
--   Von Neumann
-- statement:
--   Definitions and structural lemmas for Von Neumann, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_SpectralSet_Basic
set_option autoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


