-- Prove2me | solution 1 for Auto.sourceGaussianPairing_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:58:53.776353+00:00
-- url     : https://prove2.me/submissions/74dedb22-076a-4a7e-b538-b8547ebb8294

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_Kern_odd

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
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (q : (ℝ × ℝ) × ℝ) :
    sourceGaussianPairing F a b (triangularSpaceEquiv q) =
      -(F 0 q.1 * triangularShiftProduct (triangularPullback₁ (F 1))
        (triangularPullback₂ (F 2)) q.1 q.2 * (Kern 3 a b q.2 : ℂ)) := by
  change F 0 q.1 * F 1 (q.1.2, -q.1.1 - q.1.2 - q.2) *
      F 2 (-q.1.1 - q.1.2 - q.2, q.1.1) *
      (Kern 3 a b (q.1.1 + q.1.2 + (-q.1.1 - q.1.2 - q.2)) : ℂ) =
    -(F 0 q.1 * (F 1 (q.1.2, -(q.1.1 + q.2) - q.1.2) *
      F 2 (-q.1.1 - (q.1.2 + q.2), q.1.1)) * (Kern 3 a b q.2 : ℂ))
  rw [show q.1.1 + q.1.2 + (-q.1.1 - q.1.2 - q.2) = -q.2 by ring,
    triangular_Kern_odd ha hab, Complex.ofReal_neg]
  rw [show -(q.1.1 + q.2) - q.1.2 = -q.1.1 - q.1.2 - q.2 by ring,
    show -q.1.1 - (q.1.2 + q.2) = -q.1.1 - q.1.2 - q.2 by ring]
  ring
end Auto
