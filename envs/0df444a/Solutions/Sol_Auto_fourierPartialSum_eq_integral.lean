-- Prove2me | solution 1 for Auto.fourierPartialSum_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:52:46.613741+00:00
-- url     : https://prove2.me/submissions/e7ba1f11-7b79-457f-800b-2effe2e84268

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_dirichletKernel_periodic
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution {f : ℝ → ℂ} (hf : Continuous f) (hp : Function.Periodic f 1)
    (N : ℕ) (x : ℝ) :
    fourierPartialSum f N x = ∫ s in (-(1 / 2) : ℝ)..(1 / 2), f (x - s) * dirichletKernel N s := by
  have h₁ : fourierPartialSum f N x = ∫ t in (0 : ℝ)..1, f t * dirichletKernel N (x - t) := by
    unfold fourierPartialSum fourierCoeffOne dirichletKernel
    simp_rw [← intervalIntegral.integral_mul_const, Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum fun n _ => by
      apply Continuous.intervalIntegrable
      fun_prop]
    refine Finset.sum_congr rfl fun n _ => intervalIntegral.integral_congr fun t _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hper : Function.Periodic (fun t => f t * dirichletKernel N (x - t)) 1 := by
    intro t
    simp only
    rw [hp t, show x - (t + 1) = x - t - 1 by ring, ← dirichletKernel_periodic N (x - t - 1),
      sub_add_cancel]
  have h₂ := hper.intervalIntegral_add_eq 0 (x - 1 / 2)
  rw [zero_add] at h₂
  have h₃ : (∫ s in (-(1 / 2) : ℝ)..(1 / 2), f (x - s) * dirichletKernel N s) =
      ∫ s in (-(1 / 2) : ℝ)..(1 / 2), (fun t => f t * dirichletKernel N (x - t)) (x - s) := by
    simp
  rw [h₁, h₂, h₃, intervalIntegral.integral_comp_sub_left
    (fun t => f t * dirichletKernel N (x - t)) x]
  congr 1; ring
end Auto
