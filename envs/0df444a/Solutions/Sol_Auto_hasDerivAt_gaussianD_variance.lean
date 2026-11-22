-- Prove2me | solution 1 for Auto.hasDerivAt_gaussianD_variance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:39:17.920242+00:00
-- url     : https://prove2.me/submissions/493e75a6-5c8f-49bf-89d7-7dad3f4c6808

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
theorem _root_.solution (j : ℕ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    HasDerivAt (fun τ => gaussianD j τ t) (gaussianD (j + 2) σ t / 2) σ := by
  set c := (√(2 * π))⁻¹
  have hs : 0 < √σ := Real.sqrt_pos.2 hσ
  have hr : HasDerivAt (fun τ => (√τ)⁻¹) (-(1 / 2) * (√σ)⁻¹ ^ 3) σ := by
    have h1 := (Real.hasDerivAt_sqrt hσ.ne').inv hs.ne'
    convert h1 using 1 <;> first | rfl | field_simp
  have hF : HasDerivAt (fun τ => c * (√τ)⁻¹ ^ (j + 1) * gaussProfileD j ((√τ)⁻¹ * t)) (c * (((j + 1
      : ℕ) : ℝ) * (√σ)⁻¹ ^ j * (-(1 / 2) * (√σ)⁻¹ ^ 3)) *
          gaussProfileD j ((√σ)⁻¹ * t) +
        c * (√σ)⁻¹ ^ (j + 1) * (gaussProfileD (j + 1) ((√σ)⁻¹ * t) * (-(1 / 2) * (√σ)⁻¹ ^ 3 * t))) σ
            := by
    have h1 := (hr.pow (j + 1)).const_mul c
    have h2 := (hasDerivAt_gaussProfileD j ((√σ)⁻¹ * t)).comp σ (hr.mul_const t)
    convert h1.mul h2 using 1 <;> first | rfl | simp [Function.comp]
  have hev : (fun τ => gaussianD j τ t) =ᶠ[𝓝 σ]
      fun τ => c * (√τ)⁻¹ ^ (j + 1) * gaussProfileD j ((√τ)⁻¹ * t) := by
    filter_upwards [lt_mem_nhds hσ] with τ hτ
    exact gaussianD_eq_profile j hτ t
  refine (hF.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [gaussianD_eq_profile (j + 2) hσ, gaussProfileD_succ_succ]
  push_cast
  ring
end Auto
