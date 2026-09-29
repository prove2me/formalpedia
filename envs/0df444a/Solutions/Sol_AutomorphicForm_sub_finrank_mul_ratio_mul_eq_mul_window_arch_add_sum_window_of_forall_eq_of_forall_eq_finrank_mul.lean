-- Prove2me | solution 1 for AutomorphicForm.sub_finrank_mul_ratio_mul_eq_mul_window_arch_add_sum_window_of_forall_eq_of_forall_eq_finrank_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1d667225-355b-5b04-b29f-5d28bb79ad3c

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sub_finrank_mul_ratio_mul_eq_mul_window_arch_add_sum_window_of_forall_eq_of_forall_eq_finrank_mul

set_option autoImplicit false

open NumberField IsDedekindDomain
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hST : SK ⊆ T)

    (cG cT cG' cT' : ℝ) (hcG : 0 < cG) (hcT : 0 < cT) (hcG' : 0 < cG') (hcT' : 0 < cT')

    (Ia' Ja' Ia Ja : ℂ) (Iv' Jv' Iv Jv : HeightOneSpectrum (𝓞 K) → ℂ)

    (J' J : ℂ)
    (hJ' : J' = cG' * cT'⁻¹ * (Ja' * ∏ v ∈ T, Iv' v + Ia' * ∑ v ∈ T, Jv' v * ∏ u ∈ T.erase v, Iv' u))
    (hJ : J = cG * cT⁻¹ * (Ja * ∏ v ∈ T, Iv v + Ia * ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u))

    (hIa : Ia' = Ia) (hIv : ∀ v ∈ T, Iv' v = Iv v)
    (hJv : ∀ v ∈ T, v ∉ SK → Jv' v = (Module.finrank K L : ℂ) * Jv v) :
    J' - (Module.finrank K L : ℂ) * (((cG' * cT) / (cG * cT') : ℝ) : ℂ) * J =
      ((cG' * cT'⁻¹ : ℝ) : ℂ) *
        ((Ja' - (Module.finrank K L : ℂ) * Ja) * ∏ v ∈ T, Iv v +
          Ia * ∑ v ∈ SK, (Jv' v - (Module.finrank K L : ℂ) * Jv v) * ∏ u ∈ T.erase v, Iv u) := by
  classical
  set ℓ : ℂ := (Module.finrank K L : ℂ) with hℓ
  have hcG0 : (cG : ℂ) ≠ 0 := by exact_mod_cast hcG.ne'
  have hcT0 : (cT : ℂ) ≠ 0 := by exact_mod_cast hcT.ne'
  have hcG'0 : (cG' : ℂ) ≠ 0 := by exact_mod_cast hcG'.ne'
  have hcT'0 : (cT' : ℂ) ≠ 0 := by exact_mod_cast hcT'.ne'

  have hprod : ∏ v ∈ T, Iv' v = ∏ v ∈ T, Iv v := Finset.prod_congr rfl fun v hv => hIv v hv
  have hprod_erase : ∀ v ∈ T, ∏ u ∈ T.erase v, Iv' u = ∏ u ∈ T.erase v, Iv u := fun v _ =>
    Finset.prod_congr rfl fun u hu => hIv u (Finset.mem_of_mem_erase hu)
  have hsum' : ∑ v ∈ T, Jv' v * ∏ u ∈ T.erase v, Iv' u = ∑ v ∈ T, Jv' v * ∏ u ∈ T.erase v, Iv u :=
    Finset.sum_congr rfl fun v hv => by rw [hprod_erase v hv]

  have hsplit : ∑ v ∈ T, Jv' v * ∏ u ∈ T.erase v, Iv u - ℓ * ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u =
      ∑ v ∈ SK, (Jv' v - ℓ * Jv v) * ∏ u ∈ T.erase v, Iv u := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have h1 : ∑ v ∈ T, (Jv' v * ∏ u ∈ T.erase v, Iv u - ℓ * (Jv v * ∏ u ∈ T.erase v, Iv u)) =
        ∑ v ∈ T, (Jv' v - ℓ * Jv v) * ∏ u ∈ T.erase v, Iv u :=
      Finset.sum_congr rfl fun v _ => by ring
    rw [h1, ← Finset.sum_sdiff hST]
    have h2 : ∑ v ∈ T \ SK, (Jv' v - ℓ * Jv v) * ∏ u ∈ T.erase v, Iv u = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      rw [Finset.mem_sdiff] at hv
      rw [hJv v hv.1 hv.2, hℓ, sub_self, zero_mul]
    rw [h2, zero_add]
  rw [hJ', hJ, hIa, hprod, hsum']
  push_cast
  have key : ∀ (A P S S0 : ℂ), S - ℓ * S0 = ∑ v ∈ SK, (Jv' v - ℓ * Jv v) * ∏ u ∈ T.erase v, Iv u →
      (cG' : ℂ) * (cT' : ℂ)⁻¹ * (Ja' * P + A * S) - ℓ * ((cG' : ℂ) * cT / (cG * cT')) * ((cG : ℂ) * (cT : ℂ)⁻¹ * (Ja * P + A * S0)) =
      (cG' : ℂ) * (cT' : ℂ)⁻¹ * ((Ja' - ℓ * Ja) * P + A * ∑ v ∈ SK, (Jv' v - ℓ * Jv v) * ∏ u ∈ T.erase v, Iv u) := by
    intro A P S S0 h
    rw [← h]
    field_simp
    ring
  exact key Ia (∏ v ∈ T, Iv v) _ _ hsplit

end S_AutomorphicForm_sub_finrank_mul_ratio_mul_eq_mul_window_arch_add_sum_window_of_forall_eq_of_forall_eq_finrank_mul
end P2MW
export P2MW.S_AutomorphicForm_sub_finrank_mul_ratio_mul_eq_mul_window_arch_add_sum_window_of_forall_eq_of_forall_eq_finrank_mul (solution)
