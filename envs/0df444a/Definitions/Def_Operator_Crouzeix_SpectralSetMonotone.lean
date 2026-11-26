-- Prove2me | Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
-- name    : Operator_Crouzeix_SpectralSetMonotone
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:19:52.881147+00:00
-- url     : https://prove2.me/theorems/9dcc3e8f-2803-452e-9b94-91237e2f8174
-- title:
--   Spectral Set Monotone
-- statement:
--   Definitions and structural lemmas for Spectral Set Monotone, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetMonotone.lean

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
set_option autoImplicit false
open Set
open scoped InnerProductSpace Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


