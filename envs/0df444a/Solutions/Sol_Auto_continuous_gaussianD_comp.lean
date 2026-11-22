-- Prove2me | solution 1 for Auto.continuous_gaussianD_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:36:33.010845+00:00
-- url     : https://prove2.me/submissions/a06050e4-d56f-4980-ad20-754e25a0c064

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X]
namespace Auto
theorem _root_.solution (j : ℕ) {σ t : X → ℝ} (hσ : Continuous σ) (ht : Continuous t)
    (hpos : ∀ x, 0 < σ x) :
    Continuous (fun x => gaussianD j (σ x) (t x)) := (continuousOn_gaussianD_joint
        j).comp_continuous (hσ.prodMk ht) hpos
end Auto
