-- Prove2me | solution 1 for Auto.continuous_slice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:27:47.396805+00:00
-- url     : https://prove2.me/submissions/d77b571e-a7f2-47b8-9ae8-1112d914e061

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
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution {Q : ℝ × (Fin 3 → ℝ) → ℝ} (hQ : ContinuousOn Q (Set.Ioi 0 ×ˢ Set.univ))
    {s : ℝ} (hs : 0 < s) :
    Continuous fun p => Q (s, p) :=
  hQ.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs, trivial⟩
end Auto
