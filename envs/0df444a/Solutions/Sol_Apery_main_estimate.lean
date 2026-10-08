-- Prove2me | solution 1 for Apery.main_estimate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-04T18:46:14.367183+00:00
-- url     : https://prove2.me/submissions/7f2f1b9d-9466-4230-9510-d4574ef700cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HankelIrrationality_decay_of_normalized_family
import Theorems.Thm_Apery_natDegree_F
import Theorems.Thm_Apery_normalization
import Theorems.Thm_Apery_real_bound

open Polynomial Filter Topology MeasureTheory Apery

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∃ Q : ℤ[X],
      (∃ c' : ℚ, 0 < c' ∧ Q.map (Int.castRingHom ℚ) = C c' * F n) ∧
      Q.natDegree = 37 * n ∧
      0 < aeval zeta5 Q ∧ aeval zeta5 Q < Real.exp (-c * (n : ℝ) ^ 2) := by
  obtain ⟨m, hm, hint, hgrowth⟩ := Apery.normalization
  have hAU : (Aeff : ℝ) + (U : ℝ) < 0 := by exact_mod_cast Aeff_margin
  have hpos : ∀ᶠ n in atTop, 0 < aeval zeta5 (F n) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (real_bound n hn).1
  have hgrowth' : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (m n) ≤ ((Aeff : ℝ) + ε) * (40 * (n : ℝ)) ^ 2 := hgrowth
  have hreal : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (aeval zeta5 (F n)) ≤ ((U : ℝ) + ε) * (40 * (n : ℝ)) ^ 2 := by
    intro ε hε
    have hK : Tendsto (fun n : ℕ => (40 : ℝ) * n) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
    have hlo : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (ε / 54) * ‖x‖ :=
      Real.isLittleO_log_id_atTop.bound (by positivity)
    filter_upwards [hK.eventually hlo, hK.eventually (eventually_ge_atTop (400 / ε)),
      eventually_gt_atTop 0] with n h1 h2 hn
    have hb := (real_bound n hn).2
    set K : ℝ := 40 * (n : ℝ) with hKdef
    have hKpos : 0 < K := by positivity
    have hKr : Kr n = K := rfl
    rw [hKr] at hb
    have hlogK : Real.log K ≤ (ε / 54) * K := by
      have := h1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hKpos] at this
      exact (le_abs_self _).trans this
    have h400 : 400 ≤ ε * K := by
      have := (div_le_iff₀ hε).mp h2
      linarith
    have e1 : 27 * K * Real.log K ≤ 27 * K * ((ε / 54) * K) :=
      mul_le_mul_of_nonneg_left hlogK (by positivity)
    have e2 : 200 * K ≤ ε * K ^ 2 / 2 := by nlinarith
    nlinarith
  obtain ⟨c, hc, hdecay⟩ := HankelIrrationality.decay_of_normalized_family zeta5 F m 40
    (Aeff : ℝ) (U : ℝ) (by norm_num) hAU hm hint hgrowth' hpos hreal
  refine ⟨c, hc, ?_⟩
  filter_upwards [hdecay] with n hn
  obtain ⟨Q, ⟨c', hc', hQ⟩, hQpos, hQlt⟩ := hn
  refine ⟨Q, ⟨c', hc', hQ⟩, ?_, hQpos, hQlt⟩
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  rw [← natDegree_map_eq_of_injective hinj Q, hQ, natDegree_C_mul hc'.ne', natDegree_F]
