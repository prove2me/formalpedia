-- Prove2me | solution 1 for ALAVI.eq_45
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T21:13:06.886959+00:00
-- url     : https://prove2.me/submissions/c8a2cb03-29f7-4a94-9ec4-8eba3164518f

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_Params
import Definitions.Def_ALAVI_IsALAVIRun
import Definitions.Def_ALAVI_Lag
import Definitions.Def_ALAVI_lam
import Theorems.Thm_ALAVI_eq_41
import Theorems.Thm_ALAVI_eq_43

namespace Aux_ALAVI_eq_45

lemma eta_pos {η α γ L τ : ℝ} (hP : ALAVI.Params η α γ L τ) : 0 < η := by
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith [hP.1]

lemma eta_golden_nonneg {η α γ L τ : ℝ} (hP : ALAVI.Params η α γ L τ) :
    0 ≤ η ^ 2 + η - 1 := by
  have hη_pos := eta_pos hP
  have h1 : Real.sqrt 5 ≤ 2 * η + 1 := by linarith [hP.1]
  have hsq : (Real.sqrt 5) ^ 2 ≤ (2 * η + 1) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg 5) h1 2
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)] at hsq
  nlinarith

end Aux_ALAVI_eq_45

open ALAVI
theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ η α γ : ℝ) (v u : ℕ → E) (p q : ℕ → F)
    (hA : Standing U C G J Θ L τ) (hP : Params η α γ L τ)
    (hrun : IsALAVIRun U C G J Θ η α γ v u p q)
    (k : ℕ) (hk : 2 ≤ k) (hk1 : u (k - 1) ∈ U) (a : E) (ha : a ∈ U) (haJ : a ∈ GoldenRatioVI.Fixed.effDom J)
    (b : F) (ustar : E) :
    Lag G J Θ ustar (u k) (q k) - Lag G J Θ ustar a (q k) +
        inner ℝ (G (u k) - G ustar) (u k - a) ≤
      lam η α γ L τ v u p k a b - lam η α γ L τ v u p (k + 1) a b -
        1 / (2 * γ) * (‖b - p (k - 1)‖ ^ 2 - ‖b - p k‖ ^ 2) + τ / 2 * ‖p (k - 1) - p k‖ ^ 2 -
        η / (2 * α * (1 - η) ^ 2) * ‖v (k - 1) - v k‖ ^ 2 - τ / 2 * ‖u (k - 1) - u k‖ ^ 2 := by
  have hL_nonneg : 0 ≤ L := hA.2.2.1
  have hGLip : ∀ x ∈ U, ∀ y ∈ U, ‖G x - G y‖ ≤ L * ‖x - y‖ := hA.2.2.2.1
  have hτ : 0 < τ := hA.2.2.2.2.2.2.1
  have hη_pos : 0 < η := Aux_ALAVI_eq_45.eta_pos hP
  have hη_gold : 0 ≤ η ^ 2 + η - 1 := Aux_ALAVI_eq_45.eta_golden_nonneg hP
  have hη_lt : η < 1 := hP.2.1
  have hγ : 0 < γ := hP.2.2.1
  have hα : 0 < α := hP.2.2.2.2.1
  have hα_ub : α ≤ 1 / (2 * (γ * τ ^ 2 + L + τ) * η) := hP.2.2.2.2.2
  have hr_km1 := hrun (k - 1) (by omega)
  have hr_k := hrun k (by omega)
  have hk_eq : k - 1 + 1 = k := by omega
  have huk : u k ∈ U := by simpa [hk_eq] using hr_km1.2.2.1.1
  have huk1 : u (k + 1) ∈ U := hr_k.2.2.1.1
  have hlhs_eq : Lag G J Θ ustar (u k) (q k) - Lag G J Θ ustar a (q k) +
      inner ℝ (G (u k) - G ustar) (u k - a) =
      inner ℝ (G (u k)) (u k - a) + (J (u k)).toReal - (J a).toReal +
        inner ℝ (q k) (Θ (u k) - Θ a) := by
    unfold Lag
    rw [inner_sub_left, inner_sub_right (G ustar), inner_sub_right (q k)]
    ring
  have h41 := ALAVI.eq_41 U C G J Θ L τ η α γ v u p q hA hP hrun k hk a ha haJ
  have h43_all := ALAVI.eq_43 U C G J Θ L τ η α γ v u p q hA hP hrun k hk hk1
  have h43 : inner ℝ (q k - q (k - 1)) (Θ (u k) - Θ (u (k + 1))) ≤
      τ / 2 * ‖p (k - 1) - p k‖ ^ 2 + γ * τ ^ 2 / 2 * ‖u (k - 1) - u k‖ ^ 2 +
        (γ * τ ^ 2 + τ) / 2 * ‖u k - u (k + 1)‖ ^ 2 :=
    h43_all.1.trans (h43_all.2.1.trans h43_all.2.2)
  have h42 : inner ℝ (G (u k) - G (u (k - 1))) (u k - u (k + 1)) ≤
      L / 2 * ‖u (k - 1) - u k‖ ^ 2 + L / 2 * ‖u k - u (k + 1)‖ ^ 2 := by
    have h1 : inner ℝ (G (u k) - G (u (k - 1))) (u k - u (k + 1)) ≤
        L * ‖u (k - 1) - u k‖ * ‖u k - u (k + 1)‖ := by
      calc inner ℝ (G (u k) - G (u (k - 1))) (u k - u (k + 1))
          ≤ ‖G (u k) - G (u (k - 1))‖ * ‖u k - u (k + 1)‖ := real_inner_le_norm _ _
        _ = ‖G (u (k - 1)) - G (u k)‖ * ‖u k - u (k + 1)‖ := by rw [norm_sub_rev]
        _ ≤ (L * ‖u (k - 1) - u k‖) * ‖u k - u (k + 1)‖ :=
            mul_le_mul_of_nonneg_right (hGLip (u (k - 1)) hk1 (u k) huk) (norm_nonneg _)
    have hsq : 0 ≤ L / 2 * (‖u (k - 1) - u k‖ - ‖u k - u (k + 1)‖) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hid : L / 2 * ‖u (k - 1) - u k‖ ^ 2 + L / 2 * ‖u k - u (k + 1)‖ ^ 2 -
        L * ‖u (k - 1) - u k‖ * ‖u k - u (k + 1)‖ =
        L / 2 * (‖u (k - 1) - u k‖ - ‖u k - u (k + 1)‖) ^ 2 := by ring
    linarith
  have hv_diff_sq : 1 / (2 * α) * (1 / η * ‖u k - v k‖ ^ 2) =
      η / (2 * α * (1 - η) ^ 2) * ‖v (k - 1) - v k‖ ^ 2 := by
    have hvec : (1 - η) • (u k - v k) = η • (v k - v (k - 1)) := by
      have hvk := hr_k.1
      have h1 : (1 - η) • u k = v k - η • v (k - 1) := by
        rw [hvk]
        abel
      rw [smul_sub, h1, sub_smul, one_smul, smul_sub]
      abel
    have hnorm := congrArg (fun z : E => ‖z‖ ^ 2) hvec
    simp only [norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ 1 - η),
      Real.norm_of_nonneg hη_pos.le, mul_pow, norm_sub_rev (v k) (v (k - 1))] at hnorm
    have hα_ne : α ≠ 0 := ne_of_gt hα
    have hη_ne : η ≠ 0 := ne_of_gt hη_pos
    have h1mη_ne : 1 - η ≠ 0 := by linarith
    have hu_sq : ‖u k - v k‖ ^ 2 = η ^ 2 / (1 - η) ^ 2 * ‖v (k - 1) - v k‖ ^ 2 := by
      field_simp
      linarith
    rw [hu_sq]
    field_simp
  have hu_step_le : (γ * τ ^ 2 + L + τ) / 2 * ‖u k - u (k + 1)‖ ^ 2 -
      1 / (2 * α) * (1 / η * ‖u k - u (k + 1)‖ ^ 2) ≤
      -((γ * τ ^ 2 + L + τ) / 2 * ‖u k - u (k + 1)‖ ^ 2) := by
    set C0 := γ * τ ^ 2 + L + τ
    have hC0_pos : 0 < C0 := by
      have hgt2 : 0 ≤ γ * τ ^ 2 := mul_nonneg hγ.le (sq_nonneg _)
      linarith
    have hdenom_pos : 0 < 2 * C0 * η := mul_pos (mul_pos (by norm_num) hC0_pos) hη_pos
    have hmul1 : α * (2 * C0 * η) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hα_ub hdenom_pos.le
      have hne : 2 * C0 * η ≠ 0 := ne_of_gt hdenom_pos
      rwa [one_div_mul_cancel hne] at h
    have h2αη_pos : 0 < 2 * α * η := mul_pos (mul_pos (by norm_num) hα) hη_pos
    have hC0_le : C0 ≤ 1 / (2 * α * η) := by
      rw [le_div_iff₀ h2αη_pos]
      linarith
    have hcoeff : C0 / 2 - 1 / (2 * α * η) ≤ -(C0 / 2) := by linarith
    have hsq_nonneg : 0 ≤ ‖u k - u (k + 1)‖ ^ 2 := sq_nonneg _
    have hm := mul_le_mul_of_nonneg_right hcoeff hsq_nonneg
    have hα_ne : α ≠ 0 := ne_of_gt hα
    have hη_ne : η ≠ 0 := ne_of_gt hη_pos
    have hid : (C0 / 2 - 1 / (2 * α * η)) * ‖u k - u (k + 1)‖ ^ 2 =
        C0 / 2 * ‖u k - u (k + 1)‖ ^ 2 - 1 / (2 * α) * (1 / η * ‖u k - u (k + 1)‖ ^ 2) := by
      field_simp
    linarith
  have hgold_drop : 0 ≤ 1 / (2 * α) * ((η ^ 2 + η - 1) / η * ‖v k - u (k + 1)‖ ^ 2) :=
    mul_nonneg (div_nonneg zero_le_one (by linarith))
      (mul_nonneg (div_nonneg hη_gold hη_pos.le) (sq_nonneg _))
  have hlam_expand : lam η α γ L τ v u p k a b - lam η α γ L τ v u p (k + 1) a b -
      1 / (2 * γ) * (‖b - p (k - 1)‖ ^ 2 - ‖b - p k‖ ^ 2) =
      1 / (2 * α) * (1 / (1 - η) * ‖a - v k‖ ^ 2 - 1 / (1 - η) * ‖a - v (k + 1)‖ ^ 2) +
        (γ * τ ^ 2 + L + τ) / 2 * ‖u (k - 1) - u k‖ ^ 2 -
        (γ * τ ^ 2 + L + τ) / 2 * ‖u k - u (k + 1)‖ ^ 2 := by
    unfold lam
    have hk1_eq : k + 1 - 1 = k := by omega
    rw [hk1_eq, norm_sub_rev (v k) a, norm_sub_rev (v (k + 1)) a,
      norm_sub_rev (p (k - 1)) b, norm_sub_rev (p k) b]
    have hα_ne : α ≠ 0 := ne_of_gt hα
    have h1mη_ne : 1 - η ≠ 0 := by linarith
    field_simp
    ring
  have halg_41 : 1 / (2 * α) * (1 / (1 - η) * ‖a - v k‖ ^ 2 - 1 / (1 - η) * ‖a - v (k + 1)‖ ^ 2 -
        1 / η * ‖u k - v k‖ ^ 2 - 1 / η * ‖u k - u (k + 1)‖ ^ 2 -
        (η ^ 2 + η - 1) / η * ‖v k - u (k + 1)‖ ^ 2) =
      1 / (2 * α) * (1 / (1 - η) * ‖a - v k‖ ^ 2 - 1 / (1 - η) * ‖a - v (k + 1)‖ ^ 2) -
        1 / (2 * α) * (1 / η * ‖u k - v k‖ ^ 2) -
        1 / (2 * α) * (1 / η * ‖u k - u (k + 1)‖ ^ 2) -
        1 / (2 * α) * ((η ^ 2 + η - 1) / η * ‖v k - u (k + 1)‖ ^ 2) := by ring
  linarith [hlhs_eq, h41, h42, h43, hv_diff_sq, hu_step_le, hgold_drop, hlam_expand, halg_41]
