-- Prove2me | solution 1 for Auto.triangular_Kern_eq_primitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:43:38.702944+00:00
-- url     : https://prove2.me/submissions/fbbb93a6-963e-49ab-96ba-d940447e44a9

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_Kern_eq
public import Theorems.Thm_Auto_continuousOn_kernIntegrand_joint
public import Theorems.Thm_Auto_triangularGaussianPrimitive_hasDerivAt

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
set_option maxHeartbeats 2000000
namespace Auto
theorem _root_.solution {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {t : ℝ} (ht : t ≠ 0) :
    Kern 3 a b t = triangularGaussianPrimitive (63 / 20) b t - triangularGaussianPrimitive (63 /
      20) a t := by
  rw [Kern_eq]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    rw [Set.uIcc_of_le hab] at hs
    exact triangularGaussianPrimitive_hasDerivAt (by norm_num) (ha.trans_le hs.1) ht
  · have hcont : ContinuousOn (fun s => kernIntegrand 3 s t) (Set.Icc a b) :=
      (continuousOn_kernIntegrand_joint 3).comp
        (show ContinuousOn (fun s : ℝ => (s, t)) (Set.Icc a b) from
          (continuous_id.prodMk continuous_const).continuousOn)
        (fun s hs => show 0 < s from ha.trans_le hs.1)
    exact ContinuousOn.intervalIntegrable_of_Icc hab hcont
end Auto
