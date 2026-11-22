-- Prove2me | solution 1 for Auto.triangularHilbertTruncation_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:43:11.116382+00:00
-- url     : https://prove2.me/submissions/61e92ed6-3e4d-4628-87f0-82960d28a0dd

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_truncation_integrable
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
theorem _root_.solution (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) {ε : ℝ}
    (hε : 0 < ε) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => if ε < |q.1.1 + q.1.2 + q.2| then F₀ q.1 * F₁ (q.1.2,
      q.2) * F₂ (q.2, q.1.1) / ((q.1.1 + q.1.2 + q.2 : ℝ) : ℂ) else 0) := by
  apply (triangularSpaceEquiv_preserving.integrable_comp_emb
    triangularSpaceEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding).mp
  convert (triangular_truncation_integrable F₀ (triangularPullback₁ F₁)
    (triangularPullback₂ F₂) hε).neg using 1 <;>
    first | rfl | exact funext (triangularHilbert_integrand_comp F₀ F₁ F₂ ε)
end Auto
