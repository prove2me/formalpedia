-- Prove2me | Definitions.Def_Operator_Crouzeix_SpectralCauchy
-- name    : Operator_Crouzeix_SpectralCauchy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:04:56.105182+00:00
-- url     : https://prove2.me/theorems/dd228931-bc72-5710-b060-b71004012afc
-- title:
--   Spectral Cauchy
-- statement:
--   Definitions and structural lemmas for Spectral Cauchy, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


