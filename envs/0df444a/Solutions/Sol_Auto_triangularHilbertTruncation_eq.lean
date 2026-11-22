-- Prove2me | solution 1 for Auto.triangularHilbertTruncation_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:43:00.875259+00:00
-- url     : https://prove2.me/submissions/75f685e8-7b8e-4fbd-9580-e8a0212532c4

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularSpaceEquiv_preserving
public import Theorems.Thm_Auto_triangularHilbert_integrand_comp

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ) :
    triangularHilbertTruncation F₀ F₁ F₂ ε = -triangularTruncation F₀ (triangularPullback₁ F₁)
      (triangularPullback₂ F₂) ε := by
  unfold triangularHilbertTruncation; rw [← triangularSpaceEquiv_preserving.integral_comp
    triangularSpaceEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding]
  unfold triangularTruncation; rw [← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall (triangularHilbert_integrand_comp F₀ F₁ F₂
      ε))
end Auto
