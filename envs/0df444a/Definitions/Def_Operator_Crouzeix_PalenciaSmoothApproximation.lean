-- Prove2me | Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
-- name    : Operator_Crouzeix_PalenciaSmoothApproximation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:51:16.067336+00:00
-- url     : https://prove2.me/theorems/37354976-d461-461e-8e0a-da7eb1233440
-- title:
--   Palencia Smooth Approximation
-- statement:
--   Definitions and structural lemmas for Palencia Smooth Approximation, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSmoothApproximation.lean

import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_PalenciaExhaustion
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyMass
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionConvergence
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_NumericalRange_Convex
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]


