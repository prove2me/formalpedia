-- Prove2me | solution 1 for ALAVI.eq_38
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T21:07:41.285115+00:00
-- url     : https://prove2.me/submissions/710943ef-a8ae-4fe0-8fe9-6835316d27f3

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_Params
import Definitions.Def_ALAVI_IsALAVIRun
import Theorems.Thm_ALAVI_eq_32_optimality

namespace Aux_ALAVI_eq_38

lemma proj_mem {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (Ω : Set F) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (x : F) :
    CalamaiMore.Convergence.proj Ω x ∈ Ω := by
  unfold CalamaiMore.Convergence.proj CalamaiMore.Convergence.nearestPoint
  obtain ⟨y, hyΩ, hyd⟩ := hΩc.exists_infDist_eq_dist hΩne x
  have hex : ∃ z ∈ Ω, ∀ w ∈ Ω, ‖z - x‖ ≤ ‖w - x‖ := by
    refine ⟨y, hyΩ, fun w hw => ?_⟩
    have hw' : Metric.infDist x Ω ≤ dist x w := Metric.infDist_le_dist_of_mem hw
    rw [hyd, dist_comm x y, dist_comm x w, dist_eq_norm, dist_eq_norm] at hw'
    exact hw'
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).1

end Aux_ALAVI_eq_38

open ALAVI
theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ η α γ : ℝ) (v u : ℕ → E) (p q : ℕ → F)
    (hA : Standing U C G J Θ L τ) (hP : Params η α γ L τ)
    (hrun : IsALAVIRun U C G J Θ η α γ v u p q)
    (k : ℕ) (hk : 1 ≤ k) (a : E) (ha : a ∈ U) (haJ : a ∈ GoldenRatioVI.Fixed.effDom J) :
    inner ℝ (G (u k)) (u k - a) + (J (u k)).toReal - (J a).toReal +
        inner ℝ (q k) (Θ (u k) - Θ a) ≤
      inner ℝ (G (u k)) (u k - u (k + 1)) + (J (u k)).toReal - (J (u (k + 1))).toReal +
        inner ℝ (q k) (Θ (u k) - Θ (u (k + 1))) +
        1 / (2 * α) * (1 / (1 - η) * ‖a - v k‖ ^ 2 - 1 / (1 - η) * ‖a - v (k + 1)‖ ^ 2 -
          (η + 1) * ‖v k - u (k + 1)‖ ^ 2) := by
  have hη_lt : η < 1 := hP.2.1
  have hα : 0 < α := hP.2.2.2.2.1
  let Cstar : ProperCone ℝ F := ProperCone.innerDual (C : Set F)
  have hr_k := hrun k hk
  have hr_kp1 := hrun (k + 1) (by omega)
  have hqk : q k ∈ ProperCone.innerDual (C : Set F) := by
    rw [hr_k.2.1]
    exact Aux_ALAVI_eq_38.proj_mem (Cstar : Set F) Cstar.nonempty Cstar.isClosed _
  have h32 := ((ALAVI.eq_32_optimality U C G J Θ L τ α hA hα (G (u k)) (v k) (q k) hqk
    ⟨a, ha, haJ⟩ (u (k + 1))).mp hr_k.2.2.1).2.2 a ha haJ
  have hv_kp1 : v (k + 1) = (1 - η) • u (k + 1) + η • v k := by
    simpa using hr_kp1.1
  set X := a - v k
  set Y := u (k + 1) - v k
  have ha_sub_vk1 : a - v (k + 1) = X - (1 - η) • Y := by
    simp only [X, Y, hv_kp1, sub_smul, one_smul, smul_sub]
    abel
  have hnorm_vk1 : ‖a - v (k + 1)‖ ^ 2 =
      ‖X‖ ^ 2 - 2 * (1 - η) * inner ℝ X Y + (1 - η) ^ 2 * ‖Y‖ ^ 2 := by
    rw [ha_sub_vk1, norm_sub_sq_real, inner_smul_right, norm_smul,
      Real.norm_of_nonneg (by linarith : 0 ≤ 1 - η), mul_pow]
    ring
  have hnorm_Y : ‖v k - u (k + 1)‖ ^ 2 = ‖Y‖ ^ 2 := by
    simp only [Y]
    rw [norm_sub_rev]
  have hinner_XY : inner ℝ Y (a - u (k + 1)) = inner ℝ X Y - ‖Y‖ ^ 2 := by
    have hsub : a - u (k + 1) = X - Y := by
      simp only [X, Y]
      abel
    rw [hsub, inner_sub_right, real_inner_comm Y X, real_inner_self_eq_norm_sq]
  have hid37 : 1 / α * inner ℝ Y (a - u (k + 1)) =
      1 / (2 * α) * (1 / (1 - η) * ‖X‖ ^ 2 - 1 / (1 - η) * ‖a - v (k + 1)‖ ^ 2 -
        (η + 1) * ‖v k - u (k + 1)‖ ^ 2) := by
    have h1mη_ne : 1 - η ≠ 0 := by linarith
    have hα_ne : α ≠ 0 := ne_of_gt hα
    rw [hinner_XY, hnorm_vk1, hnorm_Y]
    field_simp
    ring
  have hg_split : inner ℝ (G (u k)) (u k - a) =
      inner ℝ (G (u k)) (u k - u (k + 1)) - inner ℝ (G (u k)) (a - u (k + 1)) := by
    have h : u k - a = (u k - u (k + 1)) - (a - u (k + 1)) := by abel
    rw [h, inner_sub_right]
  have hq_split : inner ℝ (q k) (Θ (u k) - Θ a) =
      inner ℝ (q k) (Θ (u k) - Θ (u (k + 1))) - inner ℝ (q k) (Θ a - Θ (u (k + 1))) := by
    have h : Θ (u k) - Θ a = (Θ (u k) - Θ (u (k + 1))) - (Θ a - Θ (u (k + 1))) := by abel
    rw [h, inner_sub_right]
  linarith [h32, hid37, hg_split, hq_split]
