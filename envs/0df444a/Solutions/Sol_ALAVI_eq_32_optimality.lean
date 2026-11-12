-- Prove2me | solution 1 for ALAVI.eq_32_optimality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T21:05:08.003208+00:00
-- url     : https://prove2.me/submissions/d3eef3e8-0dff-46b4-a880-27c7c9bd004a

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_IsSubproblemSol

namespace Aux_ALAVI_eq_32

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

end Aux_ALAVI_eq_32

open ALAVI
theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ α : ℝ)
    (hA : Standing U C G J Θ L τ) (hα : 0 < α) (g v : E) (q : F) (hq : q ∈ ProperCone.innerDual (C : Set F))
    (hfeas : ∃ a ∈ U, a ∈ GoldenRatioVI.Fixed.effDom J) (x : E) :
    IsSubproblemSol U J Θ α g q v x ↔
      (x ∈ U ∧ x ∈ GoldenRatioVI.Fixed.effDom J ∧
        ∀ w ∈ U, w ∈ GoldenRatioVI.Fixed.effDom J →
          0 ≤ inner ℝ g (w - x) + (J w).toReal - (J x).toReal + inner ℝ q (Θ w - Θ x) +
            1 / α * inner ℝ (x - v) (w - x)) := by
  have hUcv : Convex ℝ U := hA.2.1
  have hJbot : ∀ y, J y ≠ ⊥ := hA.2.2.2.2.1.1
  have hJcv : Convex ℝ {p : E × ℝ | J p.1 ≤ (p.2 : EReal)} := hA.2.2.2.2.1.2.2.1
  have hΘcv : IsConeConvexOn U C Θ := hA.2.2.2.2.2.1
  constructor
  · intro hsol
    rcases hsol with ⟨hxU, hmin⟩
    have hxJ : x ∈ GoldenRatioVI.Fixed.effDom J := by
      rcases hfeas with ⟨a, haU, haJ⟩
      have ha := hmin a haU
      rw [← EReal.coe_toReal haJ (hJbot a), ← EReal.coe_add] at ha
      intro htop
      rw [htop, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at ha
      exact EReal.coe_ne_top _ (top_le_iff.mp ha)
    refine ⟨hxU, hxJ, fun w hwU hwJ => ?_⟩
    have hreal_min : ∀ z ∈ U, z ∈ GoldenRatioVI.Fixed.effDom J →
        inner ℝ g x + inner ℝ q (Θ x) + ‖x - v‖ ^ 2 / (2 * α) + (J x).toReal ≤
          inner ℝ g z + inner ℝ q (Θ z) + ‖z - v‖ ^ 2 / (2 * α) + (J z).toReal := by
      intro z hzU hzJ
      have hz := hmin z hzU
      rw [← EReal.coe_toReal hxJ (hJbot x), ← EReal.coe_toReal hzJ (hJbot z),
        ← EReal.coe_add, ← EReal.coe_add] at hz
      exact EReal.coe_le_coe_iff.mp hz
    set D := inner ℝ g (w - x) + (J w).toReal - (J x).toReal + inner ℝ q (Θ w - Θ x) +
        1 / α * inner ℝ (x - v) (w - x)
    by_contra hD_neg
    push_neg at hD_neg
    set M := ‖w - x‖ ^ 2 / (2 * α) + 1
    have hM_pos : 0 < M := by
      have hnonneg : 0 ≤ ‖w - x‖ ^ 2 / (2 * α) := div_nonneg (sq_nonneg _) (by linarith)
      linarith
    set t := min (1 / 2 : ℝ) ((-D) / (2 * M))
    have ht_pos : 0 < t := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
    have ht_le_half : t ≤ 1 / 2 := min_le_left _ _
    have ht0 : 0 ≤ t := ht_pos.le
    have ht1 : t ≤ 1 := by linarith
    set wt := (1 - t) • x + t • w
    have hwtU : wt ∈ U := hUcv hxU hwU (by linarith) ht0 (by linarith)
    obtain ⟨hwtJ, hJ_wt⟩ := Aux_ALAVI_eq_32.J_segment_le hJbot hJcv hxJ hwJ ht0 ht1
    have hΘ_wt := Aux_ALAVI_eq_32.inner_Theta_segment_le hΘcv hq hxU hwU ht0 ht1
    have hg_wt : inner ℝ g wt = (1 - t) * inner ℝ g x + t * inner ℝ g w := by
      simp only [wt, inner_add_right, inner_smul_right]
    have hnorm_wt : ‖wt - v‖ ^ 2 =
        ‖x - v‖ ^ 2 + 2 * t * inner ℝ (x - v) (w - x) + t ^ 2 * ‖w - x‖ ^ 2 := by
      have hsub : wt - v = (x - v) + t • (w - x) := by
        simp only [wt, sub_smul, one_smul, smul_sub]
        abel
      rw [hsub, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg ht0, mul_pow]
      ring
    have hopt_wt := hreal_min wt hwtU hwtJ
    have hα_ne : α ≠ 0 := ne_of_gt hα
    have hdiff : 0 ≤ t * D + t ^ 2 * (‖w - x‖ ^ 2 / (2 * α)) := by
      have hJ_wt' : (J wt).toReal ≤ (1 - t) * (J x).toReal + t * (J w).toReal := hJ_wt
      have hΘ_wt' : inner ℝ q (Θ wt) ≤ (1 - t) * inner ℝ q (Θ x) + t * inner ℝ q (Θ w) := hΘ_wt
      have hnorm_wt' : ‖wt - v‖ ^ 2 / (2 * α) =
          (‖x - v‖ ^ 2 + 2 * t * inner ℝ (x - v) (w - x) + t ^ 2 * ‖w - x‖ ^ 2) / (2 * α) := by
        rw [hnorm_wt]
      have hg_sub : inner ℝ g (w - x) = inner ℝ g w - inner ℝ g x := inner_sub_right _ _ _
      have hq_sub : inner ℝ q (Θ w - Θ x) = inner ℝ q (Θ w) - inner ℝ q (Θ x) :=
        inner_sub_right _ _ _
      have hstep : inner ℝ g wt + inner ℝ q (Θ wt) + ‖wt - v‖ ^ 2 / (2 * α) + (J wt).toReal ≤
          (inner ℝ g x + inner ℝ q (Θ x) + ‖x - v‖ ^ 2 / (2 * α) + (J x).toReal) +
            t * D + t ^ 2 * (‖w - x‖ ^ 2 / (2 * α)) := by
        have halg : (1 - t) * inner ℝ g x + t * inner ℝ g w +
            ((1 - t) * inner ℝ q (Θ x) + t * inner ℝ q (Θ w)) +
            (‖x - v‖ ^ 2 + 2 * t * inner ℝ (x - v) (w - x) + t ^ 2 * ‖w - x‖ ^ 2) / (2 * α) +
            ((1 - t) * (J x).toReal + t * (J w).toReal) =
            (inner ℝ g x + inner ℝ q (Θ x) + ‖x - v‖ ^ 2 / (2 * α) + (J x).toReal) +
              t * D + t ^ 2 * (‖w - x‖ ^ 2 / (2 * α)) := by
          simp only [D, hg_sub, hq_sub]
          field_simp
          ring
        linarith [hg_wt, hΘ_wt', hnorm_wt', hJ_wt', halg]
      linarith [hopt_wt, hstep]
    have hdiv_t : 0 ≤ D + t * (‖w - x‖ ^ 2 / (2 * α)) := by
      have hpos_prod : 0 ≤ t * (D + t * (‖w - x‖ ^ 2 / (2 * α))) := by linarith
      exact nonneg_of_mul_nonneg_right hpos_prod ht_pos
    have ht_bound : t * (‖w - x‖ ^ 2 / (2 * α)) ≤ (-D) / 2 := by
      have h1 : ‖w - x‖ ^ 2 / (2 * α) ≤ M := by simp [M]
      have h2 : t ≤ (-D) / (2 * M) := min_le_right _ _
      calc t * (‖w - x‖ ^ 2 / (2 * α))
          ≤ t * M := mul_le_mul_of_nonneg_left h1 ht0
        _ ≤ ((-D) / (2 * M)) * M := mul_le_mul_of_nonneg_right h2 hM_pos.le
        _ = (-D) / 2 := by
            have hM_ne : M ≠ 0 := ne_of_gt hM_pos
            field_simp
    linarith
  · rintro ⟨hxU, hxJ, hvi⟩
    refine ⟨hxU, fun w hwU => ?_⟩
    by_cases hwJ : w ∈ GoldenRatioVI.Fixed.effDom J
    · have hw_vi := hvi w hwU hwJ
      have hnorm : ‖w - v‖ ^ 2 = ‖x - v‖ ^ 2 + 2 * inner ℝ (x - v) (w - x) + ‖w - x‖ ^ 2 := by
        have hsub : w - v = (x - v) + (w - x) := by abel
        rw [hsub, norm_add_sq_real]
      have hsq_nonneg : 0 ≤ ‖w - x‖ ^ 2 / (2 * α) := div_nonneg (sq_nonneg _) (by linarith)
      have hα_ne : α ≠ 0 := ne_of_gt hα
      have hquad : 1 / α * inner ℝ (x - v) (w - x) ≤
          ‖w - v‖ ^ 2 / (2 * α) - ‖x - v‖ ^ 2 / (2 * α) := by
        have hid : ‖w - v‖ ^ 2 / (2 * α) - ‖x - v‖ ^ 2 / (2 * α) =
            1 / α * inner ℝ (x - v) (w - x) + ‖w - x‖ ^ 2 / (2 * α) := by
          rw [hnorm]
          field_simp
          ring
        linarith
      have hg_sub : inner ℝ g (w - x) = inner ℝ g w - inner ℝ g x := inner_sub_right _ _ _
      have hq_sub : inner ℝ q (Θ w - Θ x) = inner ℝ q (Θ w) - inner ℝ q (Θ x) :=
        inner_sub_right _ _ _
      have hreal_ineq : inner ℝ g x + inner ℝ q (Θ x) + ‖x - v‖ ^ 2 / (2 * α) + (J x).toReal ≤
          inner ℝ g w + inner ℝ q (Θ w) + ‖w - v‖ ^ 2 / (2 * α) + (J w).toReal := by
        linarith
      rw [← EReal.coe_toReal hxJ (hJbot x), ← EReal.coe_toReal hwJ (hJbot w),
        ← EReal.coe_add, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr hreal_ineq
    · have htop : J w = ⊤ := not_ne_iff.mp hwJ
      rw [htop, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
      exact le_top
