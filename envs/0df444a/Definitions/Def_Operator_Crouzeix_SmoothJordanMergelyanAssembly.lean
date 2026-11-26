-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyanAssembly
-- name    : Operator_Crouzeix_SmoothJordanMergelyanAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:51:49.026144+00:00
-- url     : https://prove2.me/theorems/32c229fd-f30d-56ec-822f-f85d5b35145d
-- title:
--   Smooth Jordan Mergelyan Assembly
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Mergelyan Assembly, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyanAssembly.lean

import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


