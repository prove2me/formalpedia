-- Prove2me | solution 1 for Auto.integrable_fin2_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:31:57.487735+00:00
-- url     : https://prove2.me/submissions/a4af456c-33ef-4969-98e8-5afa0d6a1085

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
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun q : Fin 2 → ℝ => f (q 0) * g (q 1)) := by
  have := Integrable.fintype_prod (f := ![f, g]) (μ := fun _ : Fin 2 => (volume : Measure ℝ))
    (fun i => by fin_cases i; exacts [hf, hg])
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  exact this
end Auto
