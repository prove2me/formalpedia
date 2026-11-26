-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
-- name    : Operator_Crouzeix_ScalarCompanionPhaseInduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:56:52.456417+00:00
-- url     : https://prove2.me/theorems/af0b4a58-aff9-5e25-b3f5-a562659e3aee
-- title:
--   Scalar Companion Phase Induction
-- statement:
--   Definitions and structural lemmas for Scalar Companion Phase Induction, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
def CrouzeixBoundaryPhaseContractive
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : Prop :=
  ∀ xi ∈ frontier Omega.carrier,
    ‖star (Polynomial.eval xi p) +
        crouzeixPolynomialBoundaryPhaseTransform Omega xi
          (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
      polynomialSupNorm p (frontier Omega.carrier)
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


