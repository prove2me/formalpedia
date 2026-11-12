-- Prove2me | solution 1 for ALAVI.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T21:05:09.065987+00:00
-- url     : https://prove2.me/submissions/3e933182-21a1-4864-b21c-d5256d33df34

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_IsVIP
import Definitions.Def_ALAVI_IsVIS
import Definitions.Def_ALAVI_IsMVIS

namespace Aux_ALAVI_prop_4

lemma J_segment_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {J : E → EReal} (hJbot : ∀ y, J y ≠ ⊥)
    (hJcv : Convex ℝ {p : E × ℝ | J p.1 ≤ (p.2 : EReal)})
    {x w : E} (hx : x ∈ GoldenRatioVI.Fixed.effDom J) (hw : w ∈ GoldenRatioVI.Fixed.effDom J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • x + t • w ∈ GoldenRatioVI.Fixed.effDom J ∧
      (J ((1 - t) • x + t • w)).toReal ≤ (1 - t) * (J x).toReal + t * (J w).toReal := by
  have hx_mem : (x, (J x).toReal) ∈ {p : E × ℝ | J p.1 ≤ (p.2 : EReal)} := by
    show J x ≤ ((J x).toReal : EReal)
    rw [EReal.coe_toReal hx (hJbot x)]
  have hw_mem : (w, (J w).toReal) ∈ {p : E × ℝ | J p.1 ≤ (p.2 : EReal)} := by
    show J w ≤ ((J w).toReal : EReal)
    rw [EReal.coe_toReal hw (hJbot w)]
  have hseg := hJcv hx_mem hw_mem (by linarith : 0 ≤ 1 - t) ht0 (by linarith : (1 - t) + t = 1)
  simp only [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hseg
  have hne_top : J ((1 - t) • x + t • w) ≠ ⊤ := by
    intro htop
    rw [htop] at hseg
    exact EReal.coe_ne_top _ (top_le_iff.mp hseg)
  refine ⟨hne_top, ?_⟩
  rw [← EReal.coe_toReal hne_top (hJbot _)] at hseg
  exact EReal.coe_le_coe_iff.mp hseg

lemma inner_Theta_segment_le {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} {C : ProperCone ℝ F} {Θ : E → F} (hΘcv : ALAVI.IsConeConvexOn U C Θ)
    {q : F} (hq : q ∈ ProperCone.innerDual (C : Set F))
    {x w : E} (hx : x ∈ U) (hw : w ∈ U) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    inner ℝ q (Θ ((1 - t) • x + t • w)) ≤
      (1 - t) * inner ℝ q (Θ x) + t * inner ℝ q (Θ w) := by
  have hmem := hΘcv w hw x hx t ⟨ht0, ht1⟩
  have hdual := ProperCone.mem_innerDual.mp hq hmem
  have hcomm : t • w + (1 - t) • x = (1 - t) • x + t • w := add_comm _ _
  rw [hcomm, real_inner_comm] at hdual
  rw [inner_neg_right, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right] at hdual
  linarith

end Aux_ALAVI_prop_4

open ALAVI

theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ : ℝ)
    (hA : Standing U C G J Θ L τ) (a : E) (b : F) (h : IsMVIS U C G J Θ a b) :
    IsVIP U C G J Θ a ∧ IsVIS U C G J Θ a b := by
  rcases h with ⟨haU, haJ, hbC, hminty, hdual⟩
  have hUcv : Convex ℝ U := hA.2.1
  have hL_nonneg : 0 ≤ L := hA.2.2.1
  have hGLip : ∀ x ∈ U, ∀ y ∈ U, ‖G x - G y‖ ≤ L * ‖x - y‖ := hA.2.2.2.1
  have hJbot : ∀ y, J y ≠ ⊥ := hA.2.2.2.2.1.1
  have hJcv : Convex ℝ {p : E × ℝ | J p.1 ≤ (p.2 : EReal)} := hA.2.2.2.2.1.2.2.1
  have hΘcv : IsConeConvexOn U C Θ := hA.2.2.2.2.2.1
  let Cstar : ProperCone ℝ F := ProperCone.innerDual (C : Set F)
  have hb_Theta_nonneg : 0 ≤ inner ℝ b (Θ a) := by
    have h0 := hdual 0 (zero_mem Cstar)
    rw [ zero_sub, inner_neg_right, real_inner_comm] at h0
    linarith
  have hnegTheta_mem : -Θ a ∈ C := by
    rw [← ProperCone.innerDual_innerDual C, ProperCone.mem_innerDual]
    intro y hy
    have hyb : y + b ∈ Cstar := add_mem hy hbC
    have hy_ineq := hdual (y + b) hyb
    rw [add_sub_cancel_right, real_inner_comm] at hy_ineq
    rw [inner_neg_right]
    linarith
  have hb_Theta_nonpos : inner ℝ b (Θ a) ≤ 0 := by
    have h := ProperCone.mem_innerDual.mp hbC hnegTheta_mem
    rw [inner_neg_left, real_inner_comm] at h
    linarith
  have hb_Theta_zero : inner ℝ b (Θ a) = 0 := le_antisymm hb_Theta_nonpos hb_Theta_nonneg
  have hvis_vi : ∀ w ∈ U, w ∈ GoldenRatioVI.Fixed.effDom J →
      0 ≤ inner ℝ (G a) (w - a) + (J w).toReal - (J a).toReal + inner ℝ b (Θ w - Θ a) := by
    intro w hwU hwJ
    set D := inner ℝ (G a) (w - a) + (J w).toReal - (J a).toReal + inner ℝ b (Θ w - Θ a)
    by_contra hD_neg
    push_neg at hD_neg
    set M := L * ‖w - a‖ ^ 2 + 1
    have hM_pos : 0 < M := by
      have hnonneg : 0 ≤ L * ‖w - a‖ ^ 2 := mul_nonneg hL_nonneg (sq_nonneg _)
      linarith
    set t := min (1 / 2 : ℝ) ((-D) / (2 * M))
    have ht_pos : 0 < t := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
    have ht0 : 0 ≤ t := ht_pos.le
    have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
    set wt := (1 - t) • a + t • w
    have hwtU : wt ∈ U := hUcv haU hwU (by linarith) ht0 (by linarith)
    obtain ⟨hwtJ, hJ_wt⟩ := Aux_ALAVI_prop_4.J_segment_le hJbot hJcv haJ hwJ ht0 ht1
    have hΘ_wt := Aux_ALAVI_prop_4.inner_Theta_segment_le hΘcv hbC haU hwU ht0 ht1
    have hwt_sub : wt - a = t • (w - a) := by
      simp only [wt, sub_smul, one_smul, smul_sub]
      abel
    have hm_wt := hminty wt hwtU hwtJ
    rw [hwt_sub, inner_smul_right] at hm_wt
    have hG_diff : inner ℝ (G wt) (w - a) ≤ inner ℝ (G a) (w - a) + t * (L * ‖w - a‖ ^ 2) := by
      have h1 : inner ℝ (G wt) (w - a) - inner ℝ (G a) (w - a) =
          inner ℝ (G wt - G a) (w - a) := (inner_sub_left _ _ _).symm
      have h2 : inner ℝ (G wt - G a) (w - a) ≤ ‖G wt - G a‖ * ‖w - a‖ := real_inner_le_norm _ _
      have h3 : ‖G wt - G a‖ ≤ L * ‖wt - a‖ := hGLip wt hwtU a haU
      have h4 : ‖wt - a‖ = t * ‖w - a‖ := by
        rw [hwt_sub, norm_smul, Real.norm_of_nonneg ht0]
      have h5 : ‖G wt - G a‖ * ‖w - a‖ ≤ (L * (t * ‖w - a‖)) * ‖w - a‖ := by
        rw [← h4]
        exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      have h6 : (L * (t * ‖w - a‖)) * ‖w - a‖ = t * (L * ‖w - a‖ ^ 2) := by ring
      linarith
    have hb_sub1 : inner ℝ b (Θ wt - Θ a) = inner ℝ b (Θ wt) - inner ℝ b (Θ a) :=
      inner_sub_right _ _ _
    have hb_sub2 : inner ℝ b (Θ w - Θ a) = inner ℝ b (Θ w) - inner ℝ b (Θ a) :=
      inner_sub_right _ _ _
    have hquad : 0 ≤ t * D + t ^ 2 * (L * ‖w - a‖ ^ 2) := by
      have hG_mul := mul_le_mul_of_nonneg_left hG_diff ht0
      have halg : t * (inner ℝ (G a) (w - a) + t * (L * ‖w - a‖ ^ 2)) +
          ((1 - t) * (J a).toReal + t * (J w).toReal) - (J a).toReal +
          ((1 - t) * inner ℝ b (Θ a) + t * inner ℝ b (Θ w) - inner ℝ b (Θ a)) =
          t * D + t ^ 2 * (L * ‖w - a‖ ^ 2) := by
        simp only [D, hb_sub2]
        ring
      linarith [hm_wt, hG_mul, hJ_wt, hΘ_wt, hb_sub1, halg]
    have hdiv_t : 0 ≤ D + t * (L * ‖w - a‖ ^ 2) := by
      have hp : 0 ≤ t * (D + t * (L * ‖w - a‖ ^ 2)) := by linarith
      exact nonneg_of_mul_nonneg_right hp ht_pos
    have ht_bound : t * (L * ‖w - a‖ ^ 2) ≤ (-D) / 2 := by
      have h1 : L * ‖w - a‖ ^ 2 ≤ M := by simp [M]
      have h2 : t ≤ (-D) / (2 * M) := min_le_right _ _
      calc t * (L * ‖w - a‖ ^ 2)
          ≤ t * M := mul_le_mul_of_nonneg_left h1 ht0
        _ ≤ ((-D) / (2 * M)) * M := mul_le_mul_of_nonneg_right h2 hM_pos.le
        _ = (-D) / 2 := by
            have hM_ne : M ≠ 0 := ne_of_gt hM_pos
            field_simp
    linarith
  have hvis : IsVIS U C G J Θ a b := ⟨haU, haJ, hbC, hvis_vi, hdual⟩
  refine ⟨⟨haU, hnegTheta_mem, haJ, fun w hwU hwC hwJ => ?_⟩, hvis⟩
  have hvi_w := hvis_vi w hwU hwJ
  have hbw_nonpos : inner ℝ b (Θ w) ≤ 0 := by
    have h := ProperCone.mem_innerDual.mp hbC hwC
    rw [inner_neg_left, real_inner_comm] at h
    linarith
  have hbw_sub : inner ℝ b (Θ w - Θ a) ≤ 0 := by
    rw [inner_sub_right, hb_Theta_zero]
    linarith
  linarith
