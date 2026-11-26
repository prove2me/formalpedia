-- Prove2me | Definitions.Def_Operator_Crouzeix_NormalProduct
-- name    : Operator_Crouzeix_NormalProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:14:02.707702+00:00
-- url     : https://prove2.me/theorems/a2b901c7-e2c2-520f-a745-fd7646c67987
-- title:
--   Normal Product
-- statement:
--   Definitions and structural lemmas for Normal Product, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalProduct.lean

import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


