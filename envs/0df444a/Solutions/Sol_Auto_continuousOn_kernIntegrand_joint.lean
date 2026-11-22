-- Prove2me | solution 1 for Auto.continuousOn_kernIntegrand_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:36:44.495123+00:00
-- url     : https://prove2.me/submissions/72b1d5bb-b0bc-4eed-9392-da4411498718

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
open Auto
noncomputable section
namespace Auto
theorem _root_.solution (m : ℕ) :
    ContinuousOn (fun z : ℝ × ℝ => kernIntegrand m z.1 z.2) {z | 0 < z.1} := by
  have hg : ContinuousOn (fun z : ℝ × ℝ => gaussianD m (63 / 20 * z.1) z.2) {z | 0 < z.1} :=
    (continuousOn_gaussianD_joint m).comp ((continuous_const.mul continuous_fst).prodMk
      continuous_snd).continuousOn fun z hz => by
        simp only [Set.mem_ofPred_eq] at hz ⊢; exact mul_pos (by norm_num) hz
  exact (((Real.continuous_sqrt.comp continuous_fst).pow m).continuousOn.mul hg).div
    continuous_fst.continuousOn fun z hz => ne_of_gt hz
end Auto
