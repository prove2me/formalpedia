-- Prove2me | Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
-- name    : Operator_Crouzeix_SpectralSetSuperset
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:43:58.681887+00:00
-- url     : https://prove2.me/theorems/a44661bf-56f2-5727-bc11-6eec60292152
-- title:
--   Spectral Set Superset
-- statement:
--   Definitions and structural lemmas for Spectral Set Superset, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


