-- Prove2me | Definitions.Def_Operator_Crouzeix_CircleCauchy
-- name    : Operator_Crouzeix_CircleCauchy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:50:01.612479+00:00
-- url     : https://prove2.me/theorems/f35efc76-c134-54a3-b1f7-50f9e4c5765d
-- title:
--   Circle Cauchy
-- statement:
--   Definitions and structural lemmas for Circle Cauchy, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
set_option autoImplicit false
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
variable [NormOneClass B]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


