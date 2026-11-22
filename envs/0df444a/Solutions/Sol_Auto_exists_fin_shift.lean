-- Prove2me | solution 1 for Auto.exists_fin_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:39:56.61501+00:00
-- url     : https://prove2.me/submissions/bcbb52e1-a4c1-46d8-97df-dd82b6c84ba2

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
theorem _root_.solution {R : ℕ} {w : ℤ} (h : |w| ≤ R) :
    ∃ i : Fin (2 * R + 1), (i : ℤ) - R = w := by
  have := neg_abs_le w
  have := le_abs_self w
  refine ⟨⟨(w + R).toNat, by omega⟩, ?_⟩
  change (((w + R).toNat : ℕ) : ℤ) - R = w
  omega
end Auto
