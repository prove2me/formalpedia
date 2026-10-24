-- Prove2me | solution 1 for ApproxIC.Deterministic.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:38:08.935295+00:00
-- url     : https://prove2.me/submissions/f1367845-ccab-44e0-9a5d-85612cce76de

import Mathlib
import Definitions.Def_ApproxIC_Deterministic_Setting
import Definitions.Def_ApproxIC_Deterministic_HardSoft
import Theorems.Thm_ApproxIC_Deterministic_posted_price_optimal
import Theorems.Thm_ApproxIC_Deterministic_hardSoft_mem_Mdset
import Theorems.Thm_ApproxIC_Deterministic_revenue_hardSoft
import Theorems.Thm_ApproxIC_Deterministic_deterministic_dominated

open MeasureTheory

namespace ApproxIC.Deterministic

lemma aic3t_f_ii (M : Model) (hM : M.Standing) (a b : ℝ) : IntervalIntegrable M.f volume a b :=
  (hM.2.2.2.1.integrable_of_forall_notMem_eq_zero (fun x hx => hM.2.2.1 x hx)).intervalIntegrable

lemma aic3t_cdfBar_cont (M : Model) (hM : M.Standing) : Continuous (cdfBar M) := by
  have : Continuous (cdf M) := intervalIntegral.continuous_primitive (aic3t_f_ii M hM) 0
  unfold cdfBar
  fun_prop

lemma aic3t_cdfBar_le_one (M : Model) (hM : M.Standing) {v : ℝ} (hv : 0 ≤ v) :
    cdfBar M v ≤ 1 := by
  unfold cdfBar cdf
  have : 0 ≤ ∫ u in (0)..v, M.f u := intervalIntegral.integral_nonneg hv (fun u _ => hM.2.1 u)
  linarith

lemma aic3t_cdfBar_zero (M : Model) : cdfBar M 0 = 1 := by
  simp [cdfBar, cdf]

/-- The continuous extension `h(p) = p F̄(p) + ∫_p^{p+ε} F̄` of `p ↦ Π(m_d(p, p+ε))`. -/
lemma aic3t_h_cont (M : Model) (hM : M.Standing) (ε : ℝ) :
    Continuous (fun p => p * cdfBar M p + ∫ v in p..(p + ε), cdfBar M v) := by
  have hc := aic3t_cdfBar_cont M hM
  have hii : ∀ a b : ℝ, IntervalIntegrable (cdfBar M) volume a b :=
    fun a b => hc.intervalIntegrable a b
  have hprim : Continuous (fun b => ∫ v in (0)..b, cdfBar M v) :=
    intervalIntegral.continuous_primitive hii 0
  have e : (fun p => p * cdfBar M p + ∫ v in p..(p + ε), cdfBar M v)
      = fun p => p * cdfBar M p + ((∫ v in (0)..(p + ε), cdfBar M v) - ∫ v in (0)..p, cdfBar M v) := by
    funext p
    rw [intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)]
  rw [e]
  have h2 : Continuous (fun p => ∫ v in (0)..(p + ε), cdfBar M v) :=
    hprim.comp (continuous_id.add continuous_const)
  exact (continuous_id.mul hc).add (h2.sub hprim)

theorem aic3_theorem_2 (M : Model) (hM : M.Assumption1) :
    (∀ ε > 0, ∃ p ∈ Set.Icc 0 M.vbar,
        hardSoft p (p + ε) ∈ Mdset M ε ∧
        (∀ m ∈ Mdset M ε, revenue M m ≤ revenue M (hardSoft p (p + ε))) ∧
        (∀ p' ∈ Set.Icc 0 M.vbar,
          revenue M (hardSoft p' (p' + ε)) ≤ revenue M (hardSoft p (p + ε)))) ∧
    (∃ c > 0, ∃ C > 0, ∃ ε0 > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε0,
        (∃ m ∈ Mdset M ε, optRev M 0 + c * ε ≤ revenue M m) ∧
        (∀ m ∈ Mdset M ε, revenue M m ≤ optRev M 0 + C * ε)) := by
  have hS : M.Standing := hM.1
  have hvb : 0 < M.vbar := hS.1
  have hne : (Set.Icc 0 M.vbar).Nonempty := ⟨0, le_rfl, hvb.le⟩
  have hcF := aic3t_cdfBar_cont M hS
  have hrev : ∀ ε, 0 ≤ ε → ∀ r ∈ Set.Icc 0 M.vbar, revenue M (hardSoft r (r + ε)) =
      r * cdfBar M r + ∫ v in r..(r + ε), cdfBar M v :=
    fun ε hε r hr => (revenue_hardSoft M hS ε hε r hr).2
  refine ⟨?_, ?_⟩
  · -- Part 1: the optimal hard/soft floor
    intro ε hε
    obtain ⟨p, hp, hpmax⟩ := isCompact_Icc.exists_isMaxOn hne
      (aic3t_h_cont M hS ε).continuousOn
    refine ⟨p, hp, hardSoft_mem_Mdset M hS ε hε.le p hp, ?_, ?_⟩
    · intro m hm
      obtain ⟨r, hr, _, hle⟩ := deterministic_dominated M hS ε hε.le m hm
      rw [hrev ε hε.le r hr] at hle
      rw [hrev ε hε.le p hp]
      exact hle.trans (hpmax hr)
    · intro p' hp'
      rw [hrev ε hε.le p hp, hrev ε hε.le p' hp']
      exact hpmax hp'
  · -- Part 2: linear gains
    have hRc : Continuous (R M) := continuous_id.mul hcF
    obtain ⟨ps, hps, hpsmax⟩ := isCompact_Icc.exists_isMaxOn hne hRc.continuousOn
    have hopt : optRev M 0 = R M ps := (posted_price_optimal M hS ps hps hpsmax).2.2.2
    -- R(ps) > 0
    have hRpos : 0 < R M ps := by
      have hcont0 : ContinuousAt (cdfBar M) 0 := hcF.continuousAt
      have : ∀ᶠ v in nhds (0:ℝ), (1:ℝ) / 2 < cdfBar M v := by
        apply hcont0.eventually (Ioi_mem_nhds _)
        rw [aic3t_cdfBar_zero]; norm_num
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 this
      set v := min (δ / 2) M.vbar with hv
      have hv0 : 0 < v := lt_min (by linarith) hvb
      have hvI : v ∈ Set.Icc 0 M.vbar := ⟨hv0.le, min_le_right _ _⟩
      have hvF : 1 / 2 < cdfBar M v := by
        apply hball
        rw [Real.dist_eq, sub_zero, abs_of_pos hv0]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have : 0 < R M v := by unfold R; exact mul_pos hv0 (by linarith)
      exact lt_of_lt_of_le this (hpsmax hvI)
    have hFps : 0 < cdfBar M ps := by
      unfold R at hRpos
      rcases lt_or_eq_of_le hps.1 with h | h
      · exact pos_of_mul_pos_right hRpos h.le
      · rw [← h] at hRpos; simp at hRpos
    set c := cdfBar M ps / 2 with hcdef
    have hc : 0 < c := by positivity
    -- continuity of F̄ at ps
    have : ∀ᶠ v in nhds ps, c < cdfBar M v := by
      apply hcF.continuousAt.eventually (Ioi_mem_nhds _)
      simp only [hcdef]; linarith
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 this
    refine ⟨c, hc, 1, one_pos, η / 2, by positivity, ?_⟩
    intro ε hε
    refine ⟨⟨hardSoft ps (ps + ε), hardSoft_mem_Mdset M hS ε hε.1.le ps hps, ?_⟩, ?_⟩
    · rw [hrev ε hε.1.le ps hps, hopt]
      unfold R
      have hint : c * ε ≤ ∫ v in ps..(ps + ε), cdfBar M v := by
        have hle : ps ≤ ps + ε := by linarith [hε.1]
        have := intervalIntegral.integral_mono_on (μ := volume) hle intervalIntegrable_const
          (hcF.intervalIntegrable ps (ps + ε)) (f := fun _ => c) (fun v hv => by
            apply le_of_lt; apply hball
            rw [Real.dist_eq, abs_of_nonneg (by linarith [hv.1])]
            linarith [hv.2, hε.2])
        simp at this
        linarith
      linarith
    · intro m hm
      obtain ⟨r, hr, _, hle⟩ := deterministic_dominated M hS ε hε.1.le m hm
      rw [hrev ε hε.1.le r hr] at hle
      have hint : ∫ v in r..(r + ε), cdfBar M v ≤ ε := by
        have hle' : r ≤ r + ε := by linarith [hε.1]
        have := intervalIntegral.integral_mono_on (μ := volume) hle'
          (hcF.intervalIntegrable r (r + ε)) intervalIntegrable_const (g := fun _ => (1:ℝ))
          (fun v hv => aic3t_cdfBar_le_one M hS (hr.1.trans hv.1))
        simp at this
        linarith
      have hRr : R M r ≤ R M ps := hpsmax hr
      rw [hopt]
      unfold R at hRr ⊢
      linarith

end ApproxIC.Deterministic

open ApproxIC.Deterministic

theorem solution (M : Model) (hM : M.Assumption1) :
    (∀ ε > 0, ∃ p ∈ Set.Icc 0 M.vbar,
        hardSoft p (p + ε) ∈ Mdset M ε ∧
        (∀ m ∈ Mdset M ε, revenue M m ≤ revenue M (hardSoft p (p + ε))) ∧
        (∀ p' ∈ Set.Icc 0 M.vbar,
          revenue M (hardSoft p' (p' + ε)) ≤ revenue M (hardSoft p (p + ε)))) ∧
    (∃ c > 0, ∃ C > 0, ∃ ε0 > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε0,
        (∃ m ∈ Mdset M ε, optRev M 0 + c * ε ≤ revenue M m) ∧
        (∀ m ∈ Mdset M ε, revenue M m ≤ optRev M 0 + C * ε)) :=
  aic3_theorem_2 M hM
