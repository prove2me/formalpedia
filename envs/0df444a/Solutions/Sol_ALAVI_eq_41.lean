-- Prove2me | solution 1 for ALAVI.eq_41
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T21:10:09.443337+00:00
-- url     : https://prove2.me/submissions/d66bbc72-5597-4b66-9148-c0b6a26d9a92

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_Params
import Definitions.Def_ALAVI_IsALAVIRun
import Theorems.Thm_ALAVI_eq_32_optimality
import Theorems.Thm_ALAVI_eq_38

namespace Aux_ALAVI_eq_41

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

lemma eta_pos {η α γ L τ : ℝ} (hP : ALAVI.Params η α γ L τ) : 0 < η := by
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith [hP.1]

end Aux_ALAVI_eq_41

open ALAVI
theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ η α γ : ℝ) (v u : ℕ → E) (p q : ℕ → F)
    (hA : Standing U C G J Θ L τ) (hP : Params η α γ L τ)
    (hrun : IsALAVIRun U C G J Θ η α γ v u p q)
    (k : ℕ) (hk : 2 ≤ k) (a : E) (ha : a ∈ U) (haJ : a ∈ GoldenRatioVI.Fixed.effDom J) :
    inner ℝ (G (u k)) (u k - a) + (J (u k)).toReal - (J a).toReal +
        inner ℝ (q k) (Θ (u k) - Θ a) ≤
      inner ℝ (G (u k) - G (u (k - 1))) (u k - u (k + 1)) +
        inner ℝ (q k - q (k - 1)) (Θ (u k) - Θ (u (k + 1))) +
        1 / (2 * α) * (1 / (1 - η) * ‖a - v k‖ ^ 2 - 1 / (1 - η) * ‖a - v (k + 1)‖ ^ 2 -
          1 / η * ‖u k - v k‖ ^ 2 - 1 / η * ‖u k - u (k + 1)‖ ^ 2 -
          (η ^ 2 + η - 1) / η * ‖v k - u (k + 1)‖ ^ 2) := by
  have hη_pos : 0 < η := Aux_ALAVI_eq_41.eta_pos hP
  have hη_lt : η < 1 := hP.2.1
  have hα : 0 < α := hP.2.2.2.2.1
  let Cstar : ProperCone ℝ F := ProperCone.innerDual (C : Set F)
  have hr_km1 := hrun (k - 1) (by omega)
  have hr_k := hrun k (by omega)
  have hk_eq : k - 1 + 1 = k := by omega
  have hq_km1 : q (k - 1) ∈ ProperCone.innerDual (C : Set F) := by
    rw [hr_km1.2.1]
    exact Aux_ALAVI_eq_41.proj_mem (Cstar : Set F) Cstar.nonempty Cstar.isClosed _
  have hqk : q k ∈ ProperCone.innerDual (C : Set F) := by
    rw [hr_k.2.1]
    exact Aux_ALAVI_eq_41.proj_mem (Cstar : Set F) Cstar.nonempty Cstar.isClosed _
  have hsol_k := (ALAVI.eq_32_optimality U C G J Θ L τ α hA hα (G (u k)) (v k) (q k) hqk
    ⟨a, ha, haJ⟩ (u (k + 1))).mp hr_k.2.2.1
  have huk1_U : u (k + 1) ∈ U := hsol_k.1
  have huk1_J : u (k + 1) ∈ GoldenRatioVI.Fixed.effDom J := hsol_k.2.1
  have hsol_km1_raw : IsSubproblemSol U J Θ α (G (u (k - 1))) (q (k - 1)) (v (k - 1)) (u k) := by
    simpa [hk_eq] using hr_km1.2.2.1
  have h39 := ((ALAVI.eq_32_optimality U C G J Θ L τ α hA hα (G (u (k - 1))) (v (k - 1)) (q (k - 1))
    hq_km1 ⟨a, ha, haJ⟩ (u k)).mp hsol_km1_raw).2.2 (u (k + 1)) huk1_U huk1_J
  have h38 := ALAVI.eq_38 U C G J Θ L τ η α γ v u p q hA hP hrun k (by omega) a ha haJ
  have hvk_rel : u k - v k = η • (u k - v (k - 1)) := by
    have hvk := hr_k.1
    rw [hvk, sub_smul, one_smul, smul_sub]
    abel
  have hinner_eta : inner ℝ (u k - v (k - 1)) (u (k + 1) - u k) =
      1 / η * inner ℝ (u k - v k) (u (k + 1) - u k) := by
    have hη_ne : η ≠ 0 := ne_of_gt hη_pos
    rw [hvk_rel, inner_smul_left, RCLike.conj_to_real]
    field_simp
  have h3pt : 2 * inner ℝ (u k - v k) (u (k + 1) - u k) =
      ‖v k - u (k + 1)‖ ^ 2 - ‖u k - v k‖ ^ 2 - ‖u k - u (k + 1)‖ ^ 2 := by
    have hsum : u (k + 1) - v k = (u k - v k) + (u (k + 1) - u k) := by abel
    have hsq := norm_add_sq_real (u k - v k) (u (k + 1) - u k)
    rw [← hsum, norm_sub_rev (u (k + 1)) (v k), norm_sub_rev (u (k + 1)) (u k)] at hsq
    linarith
  have h40_quad : 1 / α * inner ℝ (u k - v (k - 1)) (u (k + 1) - u k) =
      1 / (2 * α) * (1 / η * ‖v k - u (k + 1)‖ ^ 2 - 1 / η * ‖u k - v k‖ ^ 2 -
        1 / η * ‖u k - u (k + 1)‖ ^ 2) := by
    have hα_ne : α ≠ 0 := ne_of_gt hα
    have hη_ne : η ≠ 0 := ne_of_gt hη_pos
    rw [hinner_eta]
    have h2 : inner ℝ (u k - v k) (u (k + 1) - u k) =
        (‖v k - u (k + 1)‖ ^ 2 - ‖u k - v k‖ ^ 2 - ‖u k - u (k + 1)‖ ^ 2) / 2 := by linarith
    rw [h2]
    field_simp
  have hg_comb : inner ℝ (G (u k)) (u k - u (k + 1)) + inner ℝ (G (u (k - 1))) (u (k + 1) - u k) =
      inner ℝ (G (u k) - G (u (k - 1))) (u k - u (k + 1)) := by
    have hneg : u (k + 1) - u k = -(u k - u (k + 1)) := by abel
    rw [hneg, inner_neg_right, inner_sub_left]
    ring
  have hq_comb : inner ℝ (q k) (Θ (u k) - Θ (u (k + 1))) +
      inner ℝ (q (k - 1)) (Θ (u (k + 1)) - Θ (u k)) =
      inner ℝ (q k - q (k - 1)) (Θ (u k) - Θ (u (k + 1))) := by
    have hneg : Θ (u (k + 1)) - Θ (u k) = -(Θ (u k) - Θ (u (k + 1))) := by abel
    rw [hneg, inner_neg_right, inner_sub_left]
    ring
  have hquad_comb : 1 / (2 * α) * (1 / (1 - η) * ‖a - v k‖ ^ 2 - 1 / (1 - η) * ‖a - v (k + 1)‖ ^ 2 -
        (η + 1) * ‖v k - u (k + 1)‖ ^ 2) +
      1 / (2 * α) * (1 / η * ‖v k - u (k + 1)‖ ^ 2 - 1 / η * ‖u k - v k‖ ^ 2 -
        1 / η * ‖u k - u (k + 1)‖ ^ 2) =
      1 / (2 * α) * (1 / (1 - η) * ‖a - v k‖ ^ 2 - 1 / (1 - η) * ‖a - v (k + 1)‖ ^ 2 -
        1 / η * ‖u k - v k‖ ^ 2 - 1 / η * ‖u k - u (k + 1)‖ ^ 2 -
        (η ^ 2 + η - 1) / η * ‖v k - u (k + 1)‖ ^ 2) := by
    have hα_ne : α ≠ 0 := ne_of_gt hα
    have hη_ne : η ≠ 0 := ne_of_gt hη_pos
    have h1mη_ne : 1 - η ≠ 0 := by linarith
    field_simp
    ring
  linarith [h38, h39, h40_quad, hg_comb, hq_comb, hquad_comb]
