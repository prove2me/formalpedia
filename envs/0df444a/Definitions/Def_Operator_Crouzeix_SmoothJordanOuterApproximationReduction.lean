-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximationReduction
-- name    : Operator_Crouzeix_SmoothJordanOuterApproximationReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:53:10.555714+00:00
-- url     : https://prove2.me/theorems/0b5c65d5-61aa-59f8-b8de-338c47d9c235
-- title:
--   Smooth Jordan Outer Approximation Reduction
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Outer Approximation Reduction, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanOuterApproximationReduction.lean

import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximation
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]


