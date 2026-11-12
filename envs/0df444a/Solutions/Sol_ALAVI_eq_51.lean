-- Prove2me | solution 1 for ALAVI.eq_51
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T21:22:51.167209+00:00
-- url     : https://prove2.me/submissions/e6d1703a-f575-4e23-a3af-72acbfea80a1

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_Params
import Definitions.Def_ALAVI_IsALAVIRun
import Definitions.Def_ALAVI_IsMVIS
import Definitions.Def_ALAVI_lam
import Definitions.Def_ALAVI_rho
import Theorems.Thm_ALAVI_proposition_4
import Theorems.Thm_ALAVI_lemma_4_1

namespace Aux_ALAVI_eq_51

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

end Aux_ALAVI_eq_51

open ALAVI

theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ η α γ : ℝ) (v u : ℕ → E) (p q : ℕ → F)
    (hA : Standing U C G J Θ L τ) (hP : Params η α γ L τ)
    (hrun : IsALAVIRun U C G J Θ η α γ v u p q)
    (k : ℕ) (hk : 2 ≤ k) (hk1 : u (k - 1) ∈ U) (a : E) (b : F) (hab : IsMVIS U C G J Θ a b) :
    rho η α γ τ * (‖v (k - 1) - v k‖ ^ 2 + ‖u (k - 1) - u k‖ ^ 2 + ‖p (k - 1) - p k‖ ^ 2 +
          ‖p k - q k‖ ^ 2) ≤
      lam η α γ L τ v u p k a b - lam η α γ L τ v u p (k + 1) a b := by
  have hJbot : ∀ y, J y ≠ ⊥ := hA.2.2.2.2.1.1
  have hnegTheta_a : -Θ a ∈ C := (ALAVI.proposition_4 U C G J Θ L τ hA a b hab).1.2.1
  rcases hab with ⟨haU, haJ, hbC, hminty, hdual⟩
  have hlem := (ALAVI.lemma_4_1 U C G J Θ L τ η α γ v u p q hA hP hrun k hk hk1 a haU haJ b hbC a).2
  have hr_km1 := hrun (k - 1) (by omega)
  have hr_k := hrun k (by omega)
  have hk_eq : k - 1 + 1 = k := by omega
  have hsol_km1 : IsSubproblemSol U J Θ α (G (u (k - 1))) (q (k - 1)) (v (k - 1)) (u k) := by
    simpa [hk_eq] using hr_km1.2.2.1
  have huk_U : u k ∈ U := hsol_km1.1
  have huk_J : u k ∈ GoldenRatioVI.Fixed.effDom J := by
    have hmin_a := hsol_km1.2 a haU
    rw [← EReal.coe_toReal haJ (hJbot a), ← EReal.coe_add] at hmin_a
    intro htop
    rw [htop, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at hmin_a
    exact EReal.coe_ne_top _ (top_le_iff.mp hmin_a)
  have hm_uk := hminty (u k) huk_U huk_J
  let Cstar : ProperCone ℝ F := ProperCone.innerDual (C : Set F)
  have hb_Theta_nonneg : 0 ≤ inner ℝ b (Θ a) := by
    have h0 := hdual 0 (zero_mem Cstar)
    rw [zero_sub, inner_neg_right, real_inner_comm] at h0
    linarith
  have hqk : q k ∈ ProperCone.innerDual (C : Set F) := by
    rw [hr_k.2.1]
    exact Aux_ALAVI_eq_51.proj_mem (Cstar : Set F) Cstar.nonempty Cstar.isClosed _
  have hqk_Theta_nonpos : inner ℝ (q k) (Θ a) ≤ 0 := by
    have h := ProperCone.mem_innerDual.mp hqk hnegTheta_a
    rw [inner_neg_left, real_inner_comm] at h
    linarith
  have hlag_decomp : (Lag G J Θ a (u k) b - Lag G J Θ a a (q k)) +
      inner ℝ (G (u k) - G a) (u k - a) =
      (inner ℝ (G (u k)) (u k - a) + (J (u k)).toReal - (J a).toReal +
        inner ℝ b (Θ (u k) - Θ a)) + inner ℝ b (Θ a) - inner ℝ (q k) (Θ a) := by
    unfold Lag
    rw [inner_sub_left, inner_sub_right (G a), inner_sub_right b]
    ring
  linarith [hlem, hm_uk, hb_Theta_nonneg, hqk_Theta_nonpos, hlag_decomp]
