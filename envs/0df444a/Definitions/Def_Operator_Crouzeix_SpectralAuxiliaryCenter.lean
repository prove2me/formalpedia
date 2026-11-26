-- Prove2me | Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
-- name    : Operator_Crouzeix_SpectralAuxiliaryCenter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:09:41.972332+00:00
-- url     : https://prove2.me/theorems/275efa27-abd3-481d-bbb7-a2344c341802
-- title:
--   Spectral Auxiliary Center
-- statement:
--   Definitions and structural lemmas for Spectral Auxiliary Center, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


