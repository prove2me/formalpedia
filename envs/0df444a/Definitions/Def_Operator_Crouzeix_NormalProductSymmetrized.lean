-- Prove2me | Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
-- name    : Operator_Crouzeix_NormalProductSymmetrized
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:42:53.245338+00:00
-- url     : https://prove2.me/theorems/2d6892d9-c2e7-4bd4-b4b8-d25784c77b1a
-- title:
--   Normal Product Symmetrized
-- statement:
--   Definitions and structural lemmas for Normal Product Symmetrized, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProductSymmetrized.lean

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


