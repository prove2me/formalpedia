-- Prove2me | Definitions.Def_Operator_Crouzeix_Palencia
-- name    : Operator_Crouzeix_Palencia
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:45:15.010858+00:00
-- url     : https://prove2.me/theorems/75740db0-10d2-578c-9c0d-8b7c9444772d
-- title:
--   Palencia
-- statement:
--   Definitions and structural lemmas for Palencia, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]


