-- Prove2me | solution 1 for Auto.gaussianD_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:03:26.836161+00:00
-- url     : https://prove2.me/submissions/af986546-5134-4b64-a30d-cde95be840bd

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
open Real
namespace Auto
theorem _root_.solution (j : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 < s) (t : ℝ) :
    gaussianD j (a * s) t = (√s)⁻¹ ^ (j + 1) * gaussianD j a ((√s)⁻¹ * t) := by
  rw [gaussianD_eq_profile j (mul_pos ha hs), gaussianD_eq_profile j ha,
    Real.sqrt_mul ha.le, mul_inv]
  rw [show (√a)⁻¹ * ((√s)⁻¹ * t) = (√a)⁻¹ * (√s)⁻¹ * t by ring]
  ring
end Auto
