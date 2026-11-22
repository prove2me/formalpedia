-- Prove2me | solution 1 for Auto.triangularGaussianPrimitive_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:41:59.370877+00:00
-- url     : https://prove2.me/submissions/9272d796-463d-40e0-b71d-ecae3b80fb63

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_gaussian_third

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
theorem _root_.solution {c s t : ℝ} (hc : 0 < c) (hs : 0 < s)
    (ht : t ≠ 0) :
    HasDerivAt (fun u => triangularGaussianPrimitive c u t) (Real.sqrt s ^ 3 * gaussianD 3 (c *
      s) t / s) s := by
  have hd := (hasDerivAt_const s (t ^ 2)).div ((hasDerivAt_id s).const_mul c)
    (mul_ne_zero (ne_of_gt hc) (ne_of_gt hs))
  have hh := (((hasDerivAt_const s 1).sub hd).mul (hd.neg.div_const 2).exp).const_mul
    (2 / (c * Real.sqrt (2 * Real.pi * c) * t))
  convert hh using 1 <;> try rfl
  rw [triangular_gaussian_third (mul_pos hc hs), gaussian]
  rw [show 2 * Real.pi * (c * s) = (2 * Real.pi * c) * s by ring,
    Real.sqrt_mul (by positivity)]
  have he : -(t ^ 2 / (c * s)) / 2 = -(t ^ 2) / (2 * (c * s)) := by ring
  dsimp only [id_eq, Pi.neg_apply, Pi.div_apply, Pi.sub_apply, Pi.mul_apply]; rw [he]
  have hsq := Real.sq_sqrt hs.le
  have hp := Real.sqrt_pos.mpr hs
  generalize Real.sqrt s = r at *; rw [← hsq]
  generalize Real.exp (-t ^ 2 / (2 * (c * r ^ 2))) = e; field_simp; ring
end Auto
