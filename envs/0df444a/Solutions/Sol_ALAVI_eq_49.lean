-- Prove2me | solution 1 for ALAVI.eq_49
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:58:29.909475+00:00
-- url     : https://prove2.me/submissions/11cbda70-cf1c-4d88-8fa2-4070ae512e7d

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_Params
import Definitions.Def_ALAVI_IsALAVIRun
import Definitions.Def_ALAVI_Lag
import Theorems.Thm_CalamaiMore_Convergence_proj_properties
import Theorems.Thm_ALAVI_eq_47

namespace Aux_ALAVI_eq_49

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

end Aux_ALAVI_eq_49

open ALAVI
theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ η α γ : ℝ) (v u : ℕ → E) (p q : ℕ → F)
    (hA : Standing U C G J Θ L τ) (hP : Params η α γ L τ)
    (hrun : IsALAVIRun U C G J Θ η α γ v u p q)
    (k : ℕ) (hk : 2 ≤ k) (b : F) (hb : b ∈ ProperCone.innerDual (C : Set F)) (ustar : E) :
    inner ℝ (p k - q k) (Θ (u k)) ≤ -(1 / γ) * ‖p k - q k‖ ^ 2 ∧
      Lag G J Θ ustar (u k) b - Lag G J Θ ustar (u k) (q k) = inner ℝ (b - q k) (Θ (u k)) ∧
      inner ℝ (b - q k) (Θ (u k)) = inner ℝ (b - p k) (Θ (u k)) + inner ℝ (p k - q k) (Θ (u k)) ∧
      inner ℝ (b - p k) (Θ (u k)) + inner ℝ (p k - q k) (Θ (u k)) ≤
        1 / (2 * γ) * (‖b - p (k - 1)‖ ^ 2 - ‖b - p k‖ ^ 2 - ‖p (k - 1) - p k‖ ^ 2) -
          1 / γ * ‖p k - q k‖ ^ 2 := by
  have hγ : 0 < γ := hP.2.2.1
  let Cstar : ProperCone ℝ F := ProperCone.innerDual (C : Set F)
  have hr_km1 := hrun (k - 1) (by omega)
  have hr_k := hrun k (by omega)
  have hk_eq : k - 1 + 1 = k := by omega
  have hpk : p k ∈ (Cstar : Set F) := by
    have h := hr_km1.2.2.2
    rw [hk_eq] at h
    rw [h]
    exact Aux_ALAVI_eq_49.proj_mem (Cstar : Set F) Cstar.nonempty Cstar.isClosed _
  have h48 : inner ℝ (p k - q k) (Θ (u k)) ≤ -(1 / γ) * ‖p k - q k‖ ^ 2 := by
    have hvi := (CalamaiMore.Convergence.proj_properties (Cstar : Set F)
      Cstar.nonempty Cstar.isClosed Cstar.convex).1 (p k + γ • Θ (u k)) (p k) hpk
    rw [← hr_k.2.1] at hvi
    have hsub : q k - (p k + γ • Θ (u k)) = -(p k - q k) - γ • Θ (u k) := by abel
    rw [hsub, inner_sub_left, inner_neg_left, real_inner_self_eq_norm_sq, inner_smul_left,
      RCLike.conj_to_real, real_inner_comm (p k - q k) (Θ (u k))] at hvi
    have hmul : γ * inner ℝ (p k - q k) (Θ (u k)) ≤ -‖p k - q k‖ ^ 2 := by linarith
    have hdiv := (le_div_iff₀' hγ).mpr hmul
    have hγne : γ ≠ 0 := ne_of_gt hγ
    have hrhs : -‖p k - q k‖ ^ 2 / γ = -(1 / γ) * ‖p k - q k‖ ^ 2 := by field_simp
    linarith
  have hlag : Lag G J Θ ustar (u k) b - Lag G J Θ ustar (u k) (q k) =
      inner ℝ (b - q k) (Θ (u k)) := by
    unfold Lag
    rw [inner_sub_left]
    ring
  have hsplit : inner ℝ (b - q k) (Θ (u k)) =
      inner ℝ (b - p k) (Θ (u k)) + inner ℝ (p k - q k) (Θ (u k)) := by
    rw [← inner_add_left, sub_add_sub_cancel]
  have h47 := ALAVI.eq_47 U C G J Θ L τ η α γ v u p q hA hP hrun k hk b hb
  have h49 : inner ℝ (b - p k) (Θ (u k)) + inner ℝ (p k - q k) (Θ (u k)) ≤
      1 / (2 * γ) * (‖b - p (k - 1)‖ ^ 2 - ‖b - p k‖ ^ 2 - ‖p (k - 1) - p k‖ ^ 2) -
        1 / γ * ‖p k - q k‖ ^ 2 := by
    linarith [h47.1, h47.2, h48]
  exact ⟨h48, hlag, hsplit, h49⟩
