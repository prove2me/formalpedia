-- Prove2me | solution 1 for Auto.triangularHilbert_integrand_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:57:33.346356+00:00
-- url     : https://prove2.me/submissions/de0465d5-8d17-4b9c-9c5b-758151d983c0

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
theorem _root_.solution (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ)
    (q : (ℝ × ℝ) × ℝ) :
    (let r := triangularSpaceEquiv q
     if ε < |r.1.1 + r.1.2 + r.2| then
       F₀ r.1 * F₁ (r.1.2, r.2) * F₂ (r.2, r.1.1) / ((r.1.1 + r.1.2 + r.2 : ℝ) : ℂ) else 0) =
    -(if ε < |q.2| then F₀ q.1 *
      triangularShiftProduct (triangularPullback₁ F₁) (triangularPullback₂ F₂) q.1 q.2 /
        (q.2 : ℂ) else 0) := by
  have he : q.1.1 + q.1.2 + (-q.1.1 - q.1.2 - q.2) = -q.2 := by ring
  change (if ε < |q.1.1 + q.1.2 + (-q.1.1 - q.1.2 - q.2)| then _ else _) = _
  rw [he, abs_neg]
  split_ifs
  swap
  · simp only [neg_zero]
  change F₀ q.1 * F₁ (q.1.2, -q.1.1 - q.1.2 - q.2) *
      F₂ (-q.1.1 - q.1.2 - q.2, q.1.1) /
      ((q.1.1 + q.1.2 + (-q.1.1 - q.1.2 - q.2) : ℝ) : ℂ) =
    -(F₀ q.1 * (F₁ (q.1.2, -(q.1.1 + q.2) - q.1.2) *
      F₂ (-q.1.1 - (q.1.2 + q.2), q.1.1)) / (q.2 : ℂ))
  have he₁ : -(q.1.1 + q.2) - q.1.2 = -q.1.1 - q.1.2 - q.2 := by ring
  have he₂ : -q.1.1 - (q.1.2 + q.2) = -q.1.1 - q.1.2 - q.2 := by ring
  rw [he, he₁, he₂, Complex.ofReal_neg]; ring
end Auto
