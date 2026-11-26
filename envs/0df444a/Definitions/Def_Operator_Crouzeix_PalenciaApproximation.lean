-- Prove2me | Definitions.Def_Operator_Crouzeix_PalenciaApproximation
-- name    : Operator_Crouzeix_PalenciaApproximation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:46:12.60399+00:00
-- url     : https://prove2.me/theorems/b0f7821a-c189-5d1d-a4be-29b3095a81be
-- title:
--   Palencia Approximation
-- statement:
--   Definitions and structural lemmas for Palencia Approximation, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaApproximation.lean

import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open Filter
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


