-- Prove2me | solution 1 for Auto.triangular_integral_symmetrize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:44:04.114342+00:00
-- url     : https://prove2.me/submissions/b5909998-493a-461b-b4b8-6be9a905d341

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_reflection_preserving

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
theorem _root_.solution {f : (ℝ × ℝ) × ℝ → ℂ} (hf : Integrable f) :
    ∫ q, f q = (2 : ℂ)⁻¹ * ∫ q, (f q + f (q.1, -q.2)) := by
  have hi : Integrable (fun q : (ℝ × ℝ) × ℝ => f (q.1, -q.2)) :=
    triangular_reflection_preserving.integrable_comp_of_integrable hf
  have he : MeasurableEmbedding (fun q : (ℝ × ℝ) × ℝ => (q.1, -q.2)) :=
    (Homeomorph.prodCongr (Homeomorph.refl (ℝ × ℝ)) (Homeomorph.neg
        ℝ)).isClosedEmbedding.measurableEmbedding
  rw [integral_add hf hi, triangular_reflection_preserving.integral_comp he]; ring
end Auto
