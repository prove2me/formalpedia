-- Prove2me | Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
-- name    : Operator_Crouzeix_SpectralAuxiliary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:08:42.366688+00:00
-- url     : https://prove2.me/theorems/a2d90463-f5a3-59bd-9512-0b8f0a8f7b46
-- title:
--   Spectral Auxiliary
-- statement:
--   Definitions and structural lemmas for Spectral Auxiliary, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliary.lean

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex ComplexConjugate Polynomial Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


