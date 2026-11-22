-- Prove2me | solution 1 for Auto.continuousOn_Gm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:27:41.050731+00:00
-- url     : https://prove2.me/submissions/78fc53a6-9309-4784-82c3-545ad7a13e34

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_continuousOn_gaussianD_joint

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
theorem _root_.solution (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Gm β m z.1 z.2) (Set.Ioi 0 ×ˢ Set.univ) := by
  have hmap : Continuous (fun z : ℝ × (Fin 3 → ℝ) => (β * z.1, z.2 0 + z.2 1 + z.2 2)) := by
    fun_prop
  exact (continuousOn_gaussianD_joint m).comp hmap.continuousOn fun z hz => mul_pos hβ hz.1
end Auto
