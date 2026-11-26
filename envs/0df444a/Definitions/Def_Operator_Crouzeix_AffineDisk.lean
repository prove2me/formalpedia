-- Prove2me | Definitions.Def_Operator_Crouzeix_AffineDisk
-- name    : Operator_Crouzeix_AffineDisk
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:55:50.046407+00:00
-- url     : https://prove2.me/theorems/0e8622ba-cbf1-4cbc-900d-b92148e3ff28
-- title:
--   Affine Disk
-- statement:
--   Definitions and structural lemmas for Affine Disk, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineDisk.lean

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
set_option autoImplicit false
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]


