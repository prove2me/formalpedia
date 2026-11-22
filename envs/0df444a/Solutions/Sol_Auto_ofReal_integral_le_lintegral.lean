-- Prove2me | solution 1 for Auto.ofReal_integral_le_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:07:12.014843+00:00
-- url     : https://prove2.me/submissions/e55b4e3e-a6a1-473b-be4c-a69fff88c29f

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
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {n : Type*} [Fintype n] [DecidableEq n] {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
namespace Auto
theorem _root_.solution {f : Z → ℝ} (hf : Integrable f ν) :
    ENNReal.ofReal (∫ z, f z ∂ν) ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂ν := by
  have h1 : ∫ z, f z ∂ν ≤ ∫ z, max (f z) 0 ∂ν :=
    integral_mono hf (hf.sup (integrable_zero _ _ _)) fun z => le_max_left _ _
  have h2 := ofReal_integral_eq_lintegral_ofReal (hf.sup (integrable_zero _ _ _))
      (Filter.Eventually.of_forall fun z => le_max_right (f z) 0)
  simp only [Pi.sup_apply, Pi.zero_apply] at h2
  refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
  rw [h2]
  congr 1; funext z
  rcases le_total (f z) 0 with h | h
  · simp [max_eq_right h, ENNReal.ofReal_of_nonpos h]
  · simp [max_eq_left h]
end Auto
