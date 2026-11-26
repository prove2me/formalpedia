-- Prove2me | Definitions.Def_Operator_Crouzeix_ProductBase
-- name    : Operator_Crouzeix_ProductBase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:47:49.91926+00:00
-- url     : https://prove2.me/theorems/22fcf58e-0d08-5bc0-9faa-3c228bfd08b7
-- title:
--   Product Base
-- statement:
--   Definitions and structural lemmas for Product Base, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


