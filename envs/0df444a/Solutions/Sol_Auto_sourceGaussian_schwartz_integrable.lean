-- Prove2me | solution 1 for Auto.sourceGaussian_schwartz_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:46:14.710282+00:00
-- url     : https://prove2.me/submissions/7921dfbe-0874-4957-9e34-a713c872a119

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_scale_integrable
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
    Integrable (sourceGaussianIntegrand (fun v => F v) a b) := by
  have hi : Integrable (sourceGaussianPairing F a b) := by
    apply (triangularSpaceEquiv_preserving.integrable_comp_emb
      triangularSpaceEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding).mp
    convert (triangular_scale_integrable (F 0) (triangularPullback₁ (F 1))
      (triangularPullback₂ (F 2)) ha hab).neg using 1 <;>
      first | rfl | exact funext (sourceGaussianPairing_comp F ha hab)
  exact (measurePreserving_fin3Equiv.integrable_comp_emb
    fin3Equiv.measurableEmbedding).mpr hi
end Auto
