-- Prove2me | Definitions.Def_CrouzeixPalenciaSolution
-- name    : CrouzeixPalenciaSolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:42:49.184932+00:00
-- url     : https://prove2.me/theorems/fd7adeb8-82d0-57de-be55-6d313299bbb8
-- title:
--   Crouzeix Palencia Solution
-- statement:
--   Definitions and structural lemmas for Crouzeix Palencia Solution, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/CrouzeixPalenciaSolution.lean

import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
set_option autoImplicit false
open scoped InnerProductSpace Polynomial
namespace PalomarCrouzeixPalencia
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
noncomputable def numericalRange (A : E →L[ℂ] E) : Set ℂ :=
  { z | ∃ x : E, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z }
noncomputable def polynomialSupNorm (p : Polynomial ℂ) (X : Set ℂ) : ℝ :=
  ⨆ z ∈ X, ‖Polynomial.eval z p‖
def IsKPolynomialSpectralSet (A : E →L[ℂ] E) (K : ℝ) (X : Set ℂ) : Prop :=
  spectrum ℂ (A : E →L[ℂ] E) ⊆ X ∧
  ∀ p : Polynomial ℂ, ‖Polynomial.aeval A p‖ ≤ K * polynomialSupNorm p X
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
end PalomarCrouzeixPalencia


