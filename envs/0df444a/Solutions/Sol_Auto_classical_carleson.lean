-- Prove2me | solution 1 for Auto.classical_carleson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:24:56.748004+00:00
-- url     : https://prove2.me/submissions/0e32ac35-24ce-4e2a-ad63-59269c156428

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carleson
public import Theorems.Thm_Auto_fourierPartialSum_eq
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (f : ℝ → ℂ) (hf : Continuous f) (hper : Function.Periodic f 1) :
    ∀ᵐ x, Tendsto (fun N ↦ Triangular.fourierPartialSum f N x) atTop (𝓝 (f x)) := by
  simpa only [fourierPartialSum_eq] using carleson hf hper
end Auto
