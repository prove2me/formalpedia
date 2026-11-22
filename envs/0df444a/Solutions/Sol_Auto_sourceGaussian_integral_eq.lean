-- Prove2me | solution 1 for Auto.sourceGaussian_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:43:21.631067+00:00
-- url     : https://prove2.me/submissions/cc4a14b8-48fe-488c-b704-b4cb105f32bc

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularSpaceEquiv_preserving
public import Theorems.Thm_Auto_measurePreserving_fin3Equiv
public import Theorems.Thm_Auto_sourceGaussianPairing_comp

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
theorem _root_.solution (F : Fin 3 → SchwartzMap (ℝ × ℝ) ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x, sourceGaussianIntegrand (fun v => F v) a b x) =
      -(∫ q : (ℝ × ℝ) × ℝ, F 0 q.1 *
        triangularShiftProduct (triangularPullback₁ (F 1)) (triangularPullback₂ (F 2))
          q.1 q.2 * (Kern 3 a b q.2 : ℂ)) := by
  change (∫ x, sourceGaussianPairing F a b (fin3Equiv x)) = _
  rw [measurePreserving_fin3Equiv.integral_comp fin3Equiv.measurableEmbedding]
  change (∫ q, sourceGaussianPairing F a b q) = _
  conv_lhs => rw [← triangularSpaceEquiv_preserving.integral_comp
    triangularSpaceEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding]
  rw [← integral_neg]
  exact integral_congr_ae (Eventually.of_forall (sourceGaussianPairing_comp F ha hab))
end Auto
