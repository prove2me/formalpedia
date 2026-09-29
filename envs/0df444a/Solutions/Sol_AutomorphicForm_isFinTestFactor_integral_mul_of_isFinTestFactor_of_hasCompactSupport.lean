-- Prove2me | solution 1 for AutomorphicForm.isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6921dfda-23f0-5a19-9d8e-821e328efe3e

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory AutomorphicForm
open scoped Topology Pointwise

scoped instance (F : Type) [Field F] [NumberField F] : T2Space (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 F) F))

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))]
    (μ : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
    (ff g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hff : IsFinTestFactor F ff) (hgs : HasCompactSupport g) :
    IsFinTestFactor F (fun x => ∫ b, ff (x * b) * g b ∂μ) := by
  obtain ⟨hlc, hsupp⟩ := hff
  constructor
  ·
    obtain ⟨V, hV, hVf⟩ := hlc.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport hsupp
    have h1 : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ∈ V := mem_of_mem_nhds hV
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hnhds : (fun y => y * x⁻¹) ⁻¹' V ∈ 𝓝 x :=
      (continuous_mul_right x⁻¹).continuousAt.preimage_mem_nhds (by simpa using hV)
    filter_upwards [hnhds] with y hy
    show (∫ b, ff (y * b) * g b ∂μ) = ∫ b, ff (x * b) * g b ∂μ
    have hfun : (fun b => ff (y * b) * g b) = fun b => ff (x * b) * g b := by
      funext b
      have h := hVf (y * x⁻¹) hy 1 h1 (x * b)
      rw [mul_one, show y * x⁻¹ * (x * b) = y * b by simp only [mul_assoc, inv_mul_cancel_left]] at h
      rw [h]
    rw [hfun]
  ·
    refine HasCompactSupport.intro (hsupp.mul hgs.inv) fun x hx => ?_
    have hfun : (fun b => ff (x * b) * g b) = fun _ => 0 := by
      funext b
      by_contra hne
      have hgb : g b ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
      have hfb : ff (x * b) ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
      exact hx ⟨x * b, subset_tsupport _ (Function.mem_support.mpr hfb), b⁻¹,
        Set.inv_mem_inv.mpr (subset_tsupport _ (Function.mem_support.mpr hgb)), mul_inv_cancel_right x b⟩
    show (∫ b, ff (x * b) * g b ∂μ) = 0
    rw [hfun, integral_zero]

end S_AutomorphicForm_isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport
end P2MW
export P2MW.S_AutomorphicForm_isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport (solution)
