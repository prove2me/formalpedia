-- Prove2me | solution 1 for Auto.fourier_mem_trigSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:54:48.930105+00:00
-- url     : https://prove2.me/submissions/d50008db-8682-4ec8-aad7-f27d955906a2

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_fourierPartialSum_exp

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution (k : ℤ) : fourier k ∈ trigSubmodule := by
  refine ⟨k.natAbs, fun N hN x => ?_⟩
  have he : ∀ t : ℝ, fourier k (t : AddCircle (1 : ℝ)) = Complex.exp (2 * π * Complex.I * k * t) :=
    fun t => by rw [fourier_coe_apply, Complex.ofReal_one, div_one]
  simp_rw [he]
  exact fourierPartialSum_exp hN x
end Auto
