-- Prove2me | solution 1 for ApproxIC.Deterministic.deterministic_dominated
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:31:41.301548+00:00
-- url     : https://prove2.me/submissions/62f143a2-2db4-4ef0-bdb9-ddc9e399b103

import Mathlib
import Definitions.Def_ApproxIC_Deterministic_Setting
import Definitions.Def_ApproxIC_Deterministic_HardSoft

open MeasureTheory

namespace ApproxIC.Deterministic

lemma aic3_f_ii (M : Model) (hM : M.Standing) : IntervalIntegrable M.f volume 0 M.vbar := by
  apply IntegrableOn.intervalIntegrable
  rw [Set.uIcc_of_le hM.1.le]; exact hM.2.2.2.1

lemma aic3_ii_bdd_mul (M : Model) (hM : M.Standing) {g : ℝ → ℝ} (hg : Measurable g) (C : ℝ)
    (hC : ∀ x ∈ Set.Icc 0 M.vbar, |g x| ≤ C) :
    IntervalIntegrable (fun x => g x * M.f x) volume 0 M.vbar := by
  have hf := aic3_f_ii M hM
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hM.1.le] at hf ⊢
  refine Integrable.bdd_mul (c := C) hf hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa using hC x (Set.Ioc_subset_Icc_self hx)

lemma aic3_t_bound (M : Model) (ε : ℝ) (m : Mech) (hm : m ∈ Mset M ε) :
    ∀ v ∈ Set.Icc 0 M.vbar, |m.t v| ≤ |m.t 0| + |ε| + M.vbar := by
  obtain ⟨⟨_, _, hx⟩, hIR, hIC⟩ := hm
  intro v hv
  have h0 : (0:ℝ) ∈ Set.Icc 0 M.vbar := ⟨le_rfl, hv.1.trans hv.2⟩
  have h1 := hIC 0 h0 v hv
  have h2 := hIR v hv
  have hx1 := hx v hv
  have hx0 := hx 0 h0
  have : v * m.x v ≤ M.vbar := by nlinarith [hv.1, hv.2, hx1.1, hx1.2]
  rw [abs_le]; constructor
  · have := neg_abs_le (m.t 0); have := le_abs_self ε; have := abs_nonneg ε
    simp only [zero_mul, zero_sub] at h1
    linarith [hv.1, hv.2]
  · have := abs_nonneg (m.t 0); have := abs_nonneg ε; linarith

lemma aic3_hs_meas (p s : ℝ) : Measurable (hardSoft p s).t := by
  show Measurable (fun v : ℝ => if v < p then (0:ℝ) else if v < s then v else s)
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Iio measurable_id measurable_const)

lemma aic3_hs_nonneg (p s v : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) (hv : 0 ≤ v) :
    0 ≤ (hardSoft p s).t v := by
  show 0 ≤ (if v < p then (0:ℝ) else if v < s then v else s)
  split_ifs <;> linarith

lemma aic3_hs_bound (p s v : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) (hv : 0 ≤ v) (C : ℝ)
    (hC1 : v ≤ C) (hC2 : s ≤ C) : |(hardSoft p s).t v| ≤ C := by
  rw [abs_of_nonneg (aic3_hs_nonneg p s v hp hs hv)]
  show (if v < p then (0:ℝ) else if v < s then v else s) ≤ C
  split_ifs <;> linarith

theorem aic3_dominated (M : Model) (hM : M.Standing) (ε : ℝ) (hε : 0 ≤ ε)
    (m : Mech) (hm : m ∈ Mdset M ε) :
    ∃ r ∈ Set.Icc 0 M.vbar,
      (∀ v ∈ Set.Icc 0 M.vbar, m.t v ≤ (hardSoft r (r + ε)).t v) ∧
      revenue M m ≤ revenue M (hardSoft r (r + ε)) := by
  obtain ⟨hmM, h01⟩ := hm
  have hmM' := hmM
  obtain ⟨⟨hxm, htm, hx⟩, hIR, hIC⟩ := hmM'
  have hvb := hM.1
  -- the pointwise domination
  have hpt : ∃ r ∈ Set.Icc 0 M.vbar,
      ∀ v ∈ Set.Icc 0 M.vbar, m.t v ≤ (hardSoft r (r + ε)).t v := by
    by_cases hS : ∃ v ∈ Set.Icc 0 M.vbar, m.x v = 1
    · set S := {v | v ∈ Set.Icc 0 M.vbar ∧ m.x v = 1} with hSdef
      obtain ⟨v0, hv0, hxv0⟩ := hS
      have hne : S.Nonempty := ⟨v0, hv0, hxv0⟩
      have hbdd : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
      have hr0 : 0 ≤ sInf S := le_csInf hne (fun x hx => hx.1.1)
      have hr1 : sInf S ≤ M.vbar := (csInf_le hbdd ⟨hv0, hxv0⟩).trans hv0.2
      refine ⟨sInf S, ⟨hr0, hr1⟩, ?_⟩
      intro v hv
      show m.t v ≤ (if v < sInf S then (0:ℝ) else if v < sInf S + ε then v else sInf S + ε)
      have hIRv := hIR v hv
      split_ifs with h1 h2
      · -- below the hard floor: x v = 0
        rcases h01 v hv with h | h
        · rw [h] at hIRv; linarith
        · exact absurd (csInf_le hbdd ⟨hv, h⟩) (not_le.2 h1)
      · rcases h01 v hv with h | h
        · rw [h] at hIRv; linarith [hv.1]
        · rw [h] at hIRv; linarith
      · rcases h01 v hv with h | h
        · rw [h] at hIRv; linarith
        · -- above the soft floor with x v = 1
          have key : m.t v - ε ≤ sInf S := by
            apply le_csInf hne
            intro w hw
            have hic := hIC v hv w hw.1
            have hirw := hIR w hw.1
            rw [hw.2] at hic hirw; rw [h] at hic
            linarith
          linarith
    · push Not at hS
      refine ⟨M.vbar, ⟨hvb.le, le_rfl⟩, ?_⟩
      intro v hv
      have hIRv := hIR v hv
      have hxv : m.x v = 0 := by
        rcases h01 v hv with h | h
        · exact h
        · exact absurd h (hS v hv)
      rw [hxv] at hIRv
      have := aic3_hs_nonneg M.vbar (M.vbar + ε) v hvb.le (by linarith) hv.1
      linarith
  obtain ⟨r, hr, hle⟩ := hpt
  refine ⟨r, hr, hle, ?_⟩
  unfold revenue
  apply intervalIntegral.integral_mono_on hvb.le
  · exact aic3_ii_bdd_mul M hM htm _ (aic3_t_bound M ε m hmM)
  · refine aic3_ii_bdd_mul M hM (aic3_hs_meas r (r + ε)) (M.vbar + ε) ?_
    intro v hv
    exact aic3_hs_bound r (r + ε) v hr.1 (by linarith [hr.1]) hv.1 _
      (by linarith [hv.2]) (by linarith [hr.2])
  · intro v hv
    exact mul_le_mul_of_nonneg_right (hle v hv) (hM.2.1 v)

end ApproxIC.Deterministic

open ApproxIC.Deterministic

theorem solution (M : Model) (hM : M.Standing) (ε : ℝ) (hε : 0 ≤ ε)
    (m : Mech) (hm : m ∈ Mdset M ε) :
    ∃ r ∈ Set.Icc 0 M.vbar,
      (∀ v ∈ Set.Icc 0 M.vbar, m.t v ≤ (hardSoft r (r + ε)).t v) ∧
      revenue M m ≤ revenue M (hardSoft r (r + ε)) :=
  aic3_dominated M hM ε hε m hm
