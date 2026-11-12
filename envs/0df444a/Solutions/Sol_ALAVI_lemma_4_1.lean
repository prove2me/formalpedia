-- Prove2me | solution 1 for ALAVI.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T21:20:15.884272+00:00
-- url     : https://prove2.me/submissions/23ee55b6-858a-487a-8ecf-8e64a8ccbc98

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_Params
import Definitions.Def_ALAVI_IsALAVIRun
import Definitions.Def_ALAVI_Lag
import Definitions.Def_ALAVI_lam
import Definitions.Def_ALAVI_rho
import Theorems.Thm_ALAVI_eq_45
import Theorems.Thm_ALAVI_eq_49

namespace Aux_ALAVI_lemma_4_1

lemma eta_pos {η α γ L τ : ℝ} (hP : ALAVI.Params η α γ L τ) : 0 < η := by
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith [hP.1]

end Aux_ALAVI_lemma_4_1

open ALAVI
theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ η α γ : ℝ) (v u : ℕ → E) (p q : ℕ → F)
    (hA : Standing U C G J Θ L τ) (hP : Params η α γ L τ)
    (hrun : IsALAVIRun U C G J Θ η α γ v u p q)
    (k : ℕ) (hk : 2 ≤ k) (hk1 : u (k - 1) ∈ U) (a : E) (ha : a ∈ U) (haJ : a ∈ GoldenRatioVI.Fixed.effDom J)
    (b : F) (hb : b ∈ ProperCone.innerDual (C : Set F)) (ustar : E) :
    0 < rho η α γ τ ∧
      (Lag G J Θ ustar (u k) b - Lag G J Θ ustar a (q k)) + inner ℝ (G (u k) - G ustar) (u k - a) +
          rho η α γ τ * (‖v (k - 1) - v k‖ ^ 2 + ‖u (k - 1) - u k‖ ^ 2 + ‖p (k - 1) - p k‖ ^ 2 +
          ‖p k - q k‖ ^ 2) ≤
        lam η α γ L τ v u p k a b - lam η α γ L τ v u p (k + 1) a b := by
  have hτ : 0 < τ := hA.2.2.2.2.2.2.1
  have hη_pos : 0 < η := Aux_ALAVI_lemma_4_1.eta_pos hP
  have hη_lt : η < 1 := hP.2.1
  have hγ : 0 < γ := hP.2.2.1
  have hγτ : γ * τ < 1 := hP.2.2.2.1
  have hα : 0 < α := hP.2.2.2.2.1
  have hc1_pos : 0 < η / (2 * α * (1 - η) ^ 2) :=
    div_pos hη_pos (mul_pos (by linarith) (sq_pos_of_pos (by linarith)))
  have hc2_pos : 0 < τ / 2 := by linarith
  have hc3_pos : 0 < (1 - τ * γ) / (2 * γ) := div_pos (by linarith) (by linarith)
  have hc4_pos : 0 < 1 / γ := one_div_pos.mpr hγ
  have hrho_pos : 0 < rho η α γ τ := by
    unfold rho
    exact lt_min (lt_min (lt_min hc1_pos hc2_pos) hc3_pos) hc4_pos
  refine ⟨hrho_pos, ?_⟩
  have h45 := ALAVI.eq_45 U C G J Θ L τ η α γ v u p q hA hP hrun k hk hk1 a ha haJ b ustar
  have h49_all := ALAVI.eq_49 U C G J Θ L τ η α γ v u p q hA hP hrun k hk b hb ustar
  have h49 : Lag G J Θ ustar (u k) b - Lag G J Θ ustar (u k) (q k) ≤
      1 / (2 * γ) * (‖b - p (k - 1)‖ ^ 2 - ‖b - p k‖ ^ 2 - ‖p (k - 1) - p k‖ ^ 2) -
        1 / γ * ‖p k - q k‖ ^ 2 := by
    linarith [h49_all.2.1, h49_all.2.2.1, h49_all.2.2.2]
  have hp_coeff : τ / 2 * ‖p (k - 1) - p k‖ ^ 2 - 1 / (2 * γ) * ‖p (k - 1) - p k‖ ^ 2 =
      -((1 - τ * γ) / (2 * γ) * ‖p (k - 1) - p k‖ ^ 2) := by
    have hγ_ne : γ ≠ 0 := ne_of_gt hγ
    field_simp
    ring
  have hr1 : rho η α γ τ ≤ η / (2 * α * (1 - η) ^ 2) :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr2 : rho η α γ τ ≤ τ / 2 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr3 : rho η α γ τ ≤ (1 - τ * γ) / (2 * γ) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hr4 : rho η α γ τ ≤ 1 / γ := min_le_right _ _
  have hm1 := mul_le_mul_of_nonneg_right hr1 (sq_nonneg ‖v (k - 1) - v k‖)
  have hm2 := mul_le_mul_of_nonneg_right hr2 (sq_nonneg ‖u (k - 1) - u k‖)
  have hm3 := mul_le_mul_of_nonneg_right hr3 (sq_nonneg ‖p (k - 1) - p k‖)
  have hm4 := mul_le_mul_of_nonneg_right hr4 (sq_nonneg ‖p k - q k‖)
  linarith [h45, h49, hp_coeff, hm1, hm2, hm3, hm4]
