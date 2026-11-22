-- Prove2me | solution 1 for Auto.continuousOn_gaussianD_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:35:23.902376+00:00
-- url     : https://prove2.me/submissions/ecbdf34d-a629-4b2c-bba6-f29db795d90b

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
namespace Auto
theorem _root_.solution (j : ℕ) :
    ContinuousOn (fun z : ℝ × ℝ => gaussianD j z.1 z.2) {z | 0 < z.1} := by
  have h : ContinuousOn (fun z : ℝ × ℝ => (√(2 * π))⁻¹ * (√z.1)⁻¹ ^ (j + 1) *
      gaussProfileD j ((√z.1)⁻¹ * z.2)) {z | 0 < z.1} := by
    have hs : ContinuousOn (fun z : ℝ × ℝ => (√z.1)⁻¹) {z | 0 < z.1} := (Real.continuous_sqrt.comp
        continuous_fst).continuousOn.inv₀ fun z hz =>
        (Real.sqrt_pos.2 hz).ne'
    exact (continuousOn_const.mul (hs.pow _)).mul ((contDiff_gaussProfileD
        j).continuous.comp_continuousOn (hs.mul continuous_snd.continuousOn))
  refine h.congr fun z hz => ?_
  exact gaussianD_eq_profile j hz z.2
end Auto
