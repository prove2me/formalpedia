-- Prove2me | solution 1 for Auto.triangular_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:57:29.753629+00:00
-- url     : https://prove2.me/submissions/b4952301-dc6a-4d5f-a98f-a7fc1a75c53a

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

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
theorem _root_.solution (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => H q.1 * triangularShiftProduct F G q.1 q.2) := by
  obtain ⟨MF, _, _, dF⟩ := triangular_schwartz_bounds F
  obtain ⟨MG, _, bG, _⟩ := triangular_schwartz_bounds G
  have hi := (triangular_integrable_decay H.integrable.norm 1 (Or.inl rfl)).const_mul
    ((MF : ℝ) * MG)
  apply hi.mono'
  · apply Measurable.aestronglyMeasurable
    unfold triangularShiftProduct
    fun_prop
  · filter_upwards [] with q
    have hb := mul_le_mul (dF (q.1.1 + q.2, q.1.2)) (bG (q.1.1, q.1.2 + q.2))
      (norm_nonneg _) (by positivity)
    dsimp at hb
    simp only [triangularShiftProduct, norm_mul, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (H q.1))]
end Auto
