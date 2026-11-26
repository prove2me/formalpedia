-- Prove2me | Definitions.Def_Operator_Crouzeix_AffineCrouzeix
-- name    : Operator_Crouzeix_AffineCrouzeix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:01:57.502574+00:00
-- url     : https://prove2.me/theorems/3e3efe77-6033-456d-b30a-edf3d3f4fd91
-- title:
--   Affine Crouzeix
-- statement:
--   Definitions and structural lemmas for Affine Crouzeix, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineCrouzeix.lean

import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
set_option autoImplicit false
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


