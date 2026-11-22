-- Prove2me | solution 1 for Auto.sum_eq_tsum_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:40:25.492824+00:00
-- url     : https://prove2.me/submissions/2189b438-1c4b-4d2f-9ee1-0fe1a37a3ce1

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
theorem _root_.solution {T E : Type*} [Fintype T] [NormedAddCommGroup E]
    {d : ℕ} (e : T → (Fin d → ℤ)) (he : Function.Injective e)
    (f : (Fin d → ℤ) → E) (hs : ∀ z, f z ≠ 0 → z ∈ Set.range e) :
    ∑ t, f (e t) = ∑' z, f z := by
  rw [← he.tsum_eq (fun z hz => hs z hz), tsum_fintype]
end Auto
