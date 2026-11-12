-- Prove2me | solution 1 for ALAVI.theorem_1_i
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T21:26:17.006088+00:00
-- url     : https://prove2.me/submissions/629d79c7-7ddd-4ca7-b9ce-f0481c2688b6

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_Params
import Definitions.Def_ALAVI_IsALAVIRun
import Definitions.Def_ALAVI_IsMVIS
import Theorems.Thm_ALAVI_eq_51
import Theorems.Thm_ALAVI_lemma_4_1

namespace Aux_ALAVI_thm_1_i

lemma lam_nonneg {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} {C : ProperCone ℝ F} {G : E → E} {J : E → EReal} {Θ : E → F}
    {η α γ L τ : ℝ} (hA : ALAVI.Standing U C G J Θ L τ)
    (hP : ALAVI.Params η α γ L τ) (v u : ℕ → E) (p : ℕ → F) (k : ℕ) (a : E) (b : F) :
    0 ≤ ALAVI.lam η α γ L τ v u p k a b := by
  have hL : 0 ≤ L := hA.2.2.1
  have hτ : 0 < τ := hA.2.2.2.2.2.2.1
  have hη_lt : η < 1 := hP.2.1
  have hγ : 0 < γ := hP.2.2.1
  have hα : 0 < α := hP.2.2.2.2.1
  unfold ALAVI.lam
  have h1 : 0 ≤ 1 / (2 * α * (1 - η)) * ‖v k - a‖ ^ 2 :=
    mul_nonneg (div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))) (sq_nonneg _)
  have h2 : 0 ≤ (γ * τ ^ 2 + L + τ) / 2 * ‖u (k - 1) - u k‖ ^ 2 := by
    have hgt : 0 ≤ γ * τ ^ 2 := mul_nonneg hγ.le (sq_nonneg _)
    exact mul_nonneg (div_nonneg (by linarith) (by norm_num)) (sq_nonneg _)
  have h3 : 0 ≤ 1 / (2 * γ) * ‖p (k - 1) - b‖ ^ 2 :=
    mul_nonneg (div_nonneg zero_le_one (by linarith)) (sq_nonneg _)
  linarith

end Aux_ALAVI_thm_1_i

open ALAVI

theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ η α γ : ℝ) (v u : ℕ → E) (p q : ℕ → F)
    (hA : Standing U C G J Θ L τ) (hP : Params η α γ L τ)
    (hrun : IsALAVIRun U C G J Θ η α γ v u p q)
    (hB : ∃ a b, IsMVIS U C G J Θ a b) :
    Bornology.IsBounded ((fun k => (v k, u k, p k)) '' Set.Ici 1) := by
  rcases hB with ⟨a, b, hab⟩
  have hη_lt : η < 1 := hP.2.1
  have hγ : 0 < γ := hP.2.2.1
  have hα : 0 < α := hP.2.2.2.2.1
  have hu_mem : ∀ m : ℕ, 2 ≤ m → u m ∈ U := by
    intro m hm
    have hr := hrun (m - 1) (by omega)
    have hmeq : m - 1 + 1 = m := by omega
    simpa [hmeq] using hr.2.2.1.1
  have hrho_pos : 0 < rho η α γ τ :=
    (ALAVI.lemma_4_1 U C G J Θ L τ η α γ v u p q hA hP hrun 3 (by omega)
      (hu_mem 2 (by omega)) a hab.1 hab.2.1 b hab.2.2.1 a).1
  have hlam_antitone : ∀ n : ℕ,
      lam η α γ L τ v u p (3 + n) a b ≤ lam η α γ L τ v u p 3 a b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hk : 2 ≤ 3 + n := by omega
      have hk1 : u (3 + n - 1) ∈ U := hu_mem (3 + n - 1) (by omega)
      have h51 := ALAVI.eq_51 U C G J Θ L τ η α γ v u p q hA hP hrun (3 + n) hk hk1 a b hab
      have hnonneg : 0 ≤ rho η α γ τ *
          (‖v (3 + n - 1) - v (3 + n)‖ ^ 2 + ‖u (3 + n - 1) - u (3 + n)‖ ^ 2 +
            ‖p (3 + n - 1) - p (3 + n)‖ ^ 2 + ‖p (3 + n) - q (3 + n)‖ ^ 2) :=
        mul_nonneg hrho_pos.le (by positivity)
      have hstep : lam η α γ L τ v u p (3 + (n + 1)) a b ≤ lam η α γ L τ v u p (3 + n) a b := by
        have heq : 3 + (n + 1) = (3 + n) + 1 := by omega
        rw [heq]
        linarith
      exact hstep.trans ih
  have hlam_le3 : ∀ k : ℕ, 3 ≤ k →
      lam η α γ L τ v u p k a b ≤ lam η α γ L τ v u p 3 a b := by
    intro k hk
    have h := hlam_antitone (k - 3)
    have heq : 3 + (k - 3) = k := by omega
    rwa [heq] at h
  have hlam3_nonneg : 0 ≤ lam η α γ L τ v u p 3 a b :=
    Aux_ALAVI_thm_1_i.lam_nonneg (U := U) (C := C) (G := G) (J := J) (Θ := Θ) hA hP v u p 3 a b
  set Λ₃ := lam η α γ L τ v u p 3 a b
  set Rv_tail := ‖a‖ + Real.sqrt (2 * α * (1 - η) * Λ₃)
  have hv_tail : ∀ k : ℕ, 3 ≤ k → ‖v k‖ ≤ Rv_tail := by
    intro k hk
    have hle := hlam_le3 k hk
    have hL : 0 ≤ L := hA.2.2.1
    have hτ : 0 < τ := hA.2.2.2.2.2.2.1
    have hgt : 0 ≤ γ * τ ^ 2 := mul_nonneg hγ.le (sq_nonneg _)
    have ht2 : 0 ≤ (γ * τ ^ 2 + L + τ) / 2 * ‖u (k - 1) - u k‖ ^ 2 :=
      mul_nonneg (div_nonneg (by linarith) (by norm_num)) (sq_nonneg _)
    have ht3 : 0 ≤ 1 / (2 * γ) * ‖p (k - 1) - b‖ ^ 2 :=
      mul_nonneg (div_nonneg zero_le_one (by linarith)) (sq_nonneg _)
    unfold lam at hle
    have ht1 : 1 / (2 * α * (1 - η)) * ‖v k - a‖ ^ 2 ≤ Λ₃ := by linarith
    have hc_pos : 0 < 2 * α * (1 - η) := mul_pos (by linarith) (by linarith)
    have hsq : ‖v k - a‖ ^ 2 ≤ 2 * α * (1 - η) * Λ₃ := by
      have hm := mul_le_mul_of_nonneg_left ht1 hc_pos.le
      have hα_ne : α ≠ 0 := ne_of_gt hα
      have h1mη_ne : 1 - η ≠ 0 := by linarith
      have hid : 2 * α * (1 - η) * (1 / (2 * α * (1 - η)) * ‖v k - a‖ ^ 2) = ‖v k - a‖ ^ 2 := by
        field_simp
      linarith
    have hnorm_sub : ‖v k - a‖ ≤ Real.sqrt (2 * α * (1 - η) * Λ₃) := by
      rw [← Real.sqrt_sq (norm_nonneg (v k - a))]
      exact Real.sqrt_le_sqrt hsq
    have htri : ‖v k‖ ≤ ‖a‖ + ‖v k - a‖ := by
      simpa [add_sub_cancel] using norm_add_le a (v k - a)
    linarith
  set Rv := max (max ‖v 1‖ ‖v 2‖) Rv_tail
  have hv_bdd : ∀ k : ℕ, 1 ≤ k → ‖v k‖ ≤ Rv := by
    intro k hk
    by_cases hk3 : 3 ≤ k
    · exact (hv_tail k hk3).trans (le_max_right _ _)
    · interval_cases k
      · exact (le_max_left ‖v 1‖ ‖v 2‖).trans (le_max_left _ _)
      · exact (le_max_right ‖v 1‖ ‖v 2‖).trans (le_max_left _ _)
  set Rp_tail := ‖b‖ + Real.sqrt (2 * γ * Λ₃)
  have hp_tail : ∀ m : ℕ, 2 ≤ m → ‖p m‖ ≤ Rp_tail := by
    intro m hm
    have hle := hlam_le3 (m + 1) (by omega)
    have hL : 0 ≤ L := hA.2.2.1
    have hτ : 0 < τ := hA.2.2.2.2.2.2.1
    have hgt : 0 ≤ γ * τ ^ 2 := mul_nonneg hγ.le (sq_nonneg _)
    have ht1 : 0 ≤ 1 / (2 * α * (1 - η)) * ‖v (m + 1) - a‖ ^ 2 :=
      mul_nonneg (div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))) (sq_nonneg _)
    have ht2 : 0 ≤ (γ * τ ^ 2 + L + τ) / 2 * ‖u m - u (m + 1)‖ ^ 2 :=
      mul_nonneg (div_nonneg (by linarith) (by norm_num)) (sq_nonneg _)
    unfold lam at hle
    have hmeq : m + 1 - 1 = m := by omega
    rw [hmeq] at hle
    have ht3 : 1 / (2 * γ) * ‖p m - b‖ ^ 2 ≤ Λ₃ := by linarith
    have hc_pos : 0 < 2 * γ := by linarith
    have hsq : ‖p m - b‖ ^ 2 ≤ 2 * γ * Λ₃ := by
      have hm_le := mul_le_mul_of_nonneg_left ht3 hc_pos.le
      have hγ_ne : γ ≠ 0 := ne_of_gt hγ
      have hid : 2 * γ * (1 / (2 * γ) * ‖p m - b‖ ^ 2) = ‖p m - b‖ ^ 2 := by field_simp
      linarith
    have hnorm_sub : ‖p m - b‖ ≤ Real.sqrt (2 * γ * Λ₃) := by
      rw [← Real.sqrt_sq (norm_nonneg (p m - b))]
      exact Real.sqrt_le_sqrt hsq
    have htri : ‖p m‖ ≤ ‖b‖ + ‖p m - b‖ := by
      simpa [add_sub_cancel] using norm_add_le b (p m - b)
    linarith
  set Rp := max ‖p 1‖ Rp_tail
  have hp_bdd : ∀ k : ℕ, 1 ≤ k → ‖p k‖ ≤ Rp := by
    intro k hk
    by_cases hk2 : 2 ≤ k
    · exact (hp_tail k hk2).trans (le_max_right _ _)
    · interval_cases k
      exact le_max_left _ _
  set Ru_tail := (1 + |η|) * Rv / (1 - η)
  have hu_tail : ∀ k : ℕ, 2 ≤ k → ‖u k‖ ≤ Ru_tail := by
    intro k hk
    have hvk := (hrun k (by omega)).1
    have hvec : (1 - η) • u k = v k - η • v (k - 1) := by
      rw [hvk]
      abel
    have hnorm := congrArg norm hvec
    rw [norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ 1 - η)] at hnorm
    have htri : ‖v k - η • v (k - 1)‖ ≤ ‖v k‖ + |η| * ‖v (k - 1)‖ := by
      calc ‖v k - η • v (k - 1)‖
          ≤ ‖v k‖ + ‖η • v (k - 1)‖ := norm_sub_le _ _
        _ = ‖v k‖ + |η| * ‖v (k - 1)‖ := by rw [norm_smul, Real.norm_eq_abs]
    have hvk_le : ‖v k‖ ≤ Rv := hv_bdd k (by omega)
    have hvkm1_le : ‖v (k - 1)‖ ≤ Rv := hv_bdd (k - 1) (by omega)
    have h1 : (1 - η) * ‖u k‖ ≤ (1 + |η|) * Rv := by
      have hm := mul_le_mul_of_nonneg_left hvkm1_le (abs_nonneg η)
      linarith
    exact (le_div_iff₀' (by linarith : 0 < 1 - η)).mpr h1
  set Ru := max ‖u 1‖ Ru_tail
  have hu_bdd : ∀ k : ℕ, 1 ≤ k → ‖u k‖ ≤ Ru := by
    intro k hk
    by_cases hk2 : 2 ≤ k
    · exact (hu_tail k hk2).trans (le_max_right _ _)
    · interval_cases k
      exact le_max_left _ _
  rw [Metric.isBounded_iff_subset_closedBall (0 : E × E × F)]
  refine ⟨max Rv (max Ru Rp), ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
  exact max_le ((hv_bdd k hk).trans (le_max_left _ _))
    (max_le ((hu_bdd k hk).trans ((le_max_left _ _).trans (le_max_right _ _)))
      ((hp_bdd k hk).trans ((le_max_right _ _).trans (le_max_right _ _))))
