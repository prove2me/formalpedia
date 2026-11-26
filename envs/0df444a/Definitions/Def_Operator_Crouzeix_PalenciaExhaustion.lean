-- Prove2me | Definitions.Def_Operator_Crouzeix_PalenciaExhaustion
-- name    : Operator_Crouzeix_PalenciaExhaustion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:46:59.543303+00:00
-- url     : https://prove2.me/theorems/760ec36b-72c3-4d06-a025-2207c1cfad3c
-- title:
--   Palencia Exhaustion
-- statement:
--   Definitions and structural lemmas for Palencia Exhaustion, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaExhaustion.lean

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_PalenciaApproximation
set_option autoImplicit false
open Filter Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


