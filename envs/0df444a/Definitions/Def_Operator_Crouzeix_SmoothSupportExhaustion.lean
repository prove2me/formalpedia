-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothSupportExhaustion
-- name    : Operator_Crouzeix_SmoothSupportExhaustion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:55:35.177824+00:00
-- url     : https://prove2.me/theorems/afb737c7-6113-51b9-ac0a-a3145e23551d
-- title:
--   Smooth Support Exhaustion
-- statement:
--   Definitions and structural lemmas for Smooth Support Exhaustion, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportExhaustion.lean

import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Theorems.Thm_convex_numericalRange
import Theorems.Thm_hasSmoothJordanOuterApproximationForPolytopes
import Theorems.Thm_hasSmoothJordanOuterApproximation_of_polytope_case
import Theorems.Thm_isBounded_numericalRange
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange


set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
theorem hasSmoothJordanOuterApproximation_of_isCompact_nonempty_convex
    {K : Set ℂ} (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hKconvex : Convex ℝ K) :
    HasSmoothJordanOuterApproximation K :=
  hasSmoothJordanOuterApproximation_of_polytope_case
    hKcompact hKnonempty hKconvex
      hasSmoothJordanOuterApproximationForPolytopes
noncomputable def StrictNestedSmoothJordanExhaustion.ofCompactConvex
    (K : Set ℂ) (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hKconvex : Convex ℝ K) :
    StrictNestedSmoothJordanExhaustion K :=
  StrictNestedSmoothJordanExhaustion.ofOuterApproximation
    K hKcompact hKconvex
      (hasSmoothJordanOuterApproximation_of_isCompact_nonempty_convex
        hKcompact hKnonempty hKconvex)
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem isCompact_closure_numericalRange (A : E →L[ℂ] E) :
    IsCompact (closure (numericalRange A)) := by
  exact (isBounded_numericalRange A).isCompact_closure
theorem nonempty_closure_numericalRange [Nontrivial E]
    (A : E →L[ℂ] E) : (closure (numericalRange A)).Nonempty := by
  obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hxnorm : ‖x‖ = 1 := by
    rw [Metric.mem_sphere, dist_zero_right] at hx
    exact hx
  exact ⟨⟪x, A x⟫_ℂ,
    subset_closure ((mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩)⟩
variable [Nontrivial E]
noncomputable def StrictNestedSmoothJordanExhaustion.numericalRange
    (A : E →L[ℂ] E) :
    StrictNestedSmoothJordanExhaustion
      (closure (_root_.numericalRange A)) :=
  StrictNestedSmoothJordanExhaustion.ofCompactConvex
    (closure (_root_.numericalRange A))
    (isCompact_closure_numericalRange A)
    (nonempty_closure_numericalRange A)
    (convex_numericalRange A).closure


