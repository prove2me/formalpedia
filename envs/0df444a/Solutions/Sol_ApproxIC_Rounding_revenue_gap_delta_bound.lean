-- Prove2me | solution 1 for ApproxIC.Rounding.revenue_gap_delta_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:46:35.354679+00:00
-- url     : https://prove2.me/submissions/a557c61e-79dc-4ba0-8071-718187e923e6

import Mathlib
import Definitions.Def_ApproxIC_Rounding_Setting

open MeasureTheory Set ApproxIC.Rounding

namespace AIC0Gap

/-- clamp to `[0, vbar]` -/
noncomputable def clampS (B v : ℝ) : ℝ := max 0 (min v B)

lemma clampS_mem {B : ℝ} (hB : 0 ≤ B) (v : ℝ) : clampS B v ∈ Icc 0 B :=
  ⟨le_max_left _ _, max_le hB (min_le_right _ _)⟩

lemma clampS_eq {B v : ℝ} (hv : v ∈ Icc 0 B) : clampS B v = v := by
  unfold clampS; rw [min_eq_left hv.2, max_eq_right hv.1]

lemma clampS_mono (B : ℝ) : Monotone (clampS B) := fun _ _ h =>
  max_le_max le_rfl (min_le_min h le_rfl)

lemma clampS_cont (B : ℝ) : Continuous (clampS B) := by
  unfold clampS; fun_prop

/-- measurability of a rounded mechanism given the optimality property on `S`. -/
lemma meas_of_opt (B c : ℝ) (hB : 0 ≤ B) (a b : ℝ → ℝ)
    (ha0 : ∀ v ∈ Icc 0 B, 0 ≤ a v)
    (hopt : ∀ v ∈ Icc 0 B, ∀ w ∈ Icc 0 B, v * a w - c * b w ≤ v * a v - c * b v) :
    Measurable ((Icc 0 B).indicator a) ∧
      Measurable ((Icc 0 B).indicator (fun v => c * b v)) := by
  set g : ℝ → ℝ := fun v => a (clampS B v)
  set U : ℝ → ℝ := fun v => clampS B v * a (clampS B v) - c * b (clampS B v)
  have hg : Monotone g := by
    intro v1 v2 h
    have h1 := clampS_mem hB v1
    have h2 := clampS_mem hB v2
    have hle := clampS_mono B h
    rcases hle.lt_or_eq with hlt | heq
    · have e1 := hopt _ h1 _ h2
      have e2 := hopt _ h2 _ h1
      have : (clampS B v2 - clampS B v1) * (a (clampS B v2) - a (clampS B v1)) ≥ 0 := by
        nlinarith
      have hpos : 0 < clampS B v2 - clampS B v1 := by linarith
      show a (clampS B v1) ≤ a (clampS B v2)
      by_contra hc
      push_neg at hc
      nlinarith
    · show a (clampS B v1) ≤ a (clampS B v2)
      rw [heq]
  have hU : Monotone U := by
    intro v1 v2 h
    have h1 := clampS_mem hB v1
    have h2 := clampS_mem hB v2
    have hle := clampS_mono B h
    have e := hopt _ h2 _ h1
    have hx := ha0 _ h1
    show clampS B v1 * a (clampS B v1) - c * b (clampS B v1) ≤
      clampS B v2 * a (clampS B v2) - c * b (clampS B v2)
    nlinarith
  have hgm : Measurable g := hg.measurable
  have hUm : Measurable U := hU.measurable
  have hcm : Measurable (clampS B) := (clampS_cont B).measurable
  constructor
  · have : (Icc 0 B).indicator a = (Icc 0 B).indicator g := by
      apply indicator_congr; intro v hv; simp [g, clampS_eq hv]
    rw [this]; exact hgm.indicator measurableSet_Icc
  · have : (Icc 0 B).indicator (fun v => c * b v) =
        (Icc 0 B).indicator (fun v => clampS B v * g v - U v) := by
      apply indicator_congr; intro v hv; simp [g, U, clampS_eq hv]
    rw [this]
    exact ((hcm.mul hgm).sub hUm).indicator measurableSet_Icc

lemma f_integrable (M : Model) (hM : M.Standing) : Integrable M.f := by
  obtain ⟨_, _, hz, hint, _⟩ := hM
  exact hint.integrable_of_forall_notMem_eq_zero (fun v hv => hz v hv)

/-- revenue of mechanisms in `M(0)` is at most `vbar`, and `optRev` is a genuine sup. -/
lemma bdd (M : Model) (hM : M.Standing) (ε : ℝ) :
    BddAbove (revenue M '' Mset M ε) := by
  have hv : 0 < M.vbar := hM.1
  have hf0 := hM.2.1
  have hone := hM.2.2.2.2
  refine ⟨M.vbar, ?_⟩
  rintro _ ⟨m, ⟨⟨_, _, hx⟩, hIR, _⟩, rfl⟩
  unfold revenue
  by_cases hi : IntervalIntegrable (fun v => m.t v * M.f v) volume 0 M.vbar
  · have hfi : IntervalIntegrable (fun v => M.vbar * M.f v) volume 0 M.vbar :=
      ((f_integrable M hM).intervalIntegrable).const_mul _
    calc (∫ v in (0)..M.vbar, m.t v * M.f v) ≤ ∫ v in (0)..M.vbar, M.vbar * M.f v := by
          apply intervalIntegral.integral_mono_on hv.le hi hfi
          intro v hvS
          have h1 := hIR v hvS
          have h2 := hx v hvS
          have : m.t v ≤ M.vbar := by nlinarith [hvS.1, hvS.2, h2.1, h2.2]
          exact mul_le_mul_of_nonneg_right this (hf0 v)
      _ = M.vbar := by rw [intervalIntegral.integral_const_mul, hone, mul_one]
  · rw [intervalIntegral.integral_undef hi]; exact hv.le

lemma optRev_nonneg (M : Model) (hM : M.Standing) : 0 ≤ optRev M 0 := by
  have hmem : (⟨fun _ => 0, fun _ => 0⟩ : Mech) ∈ Mset M 0 := by
    refine ⟨⟨measurable_const, measurable_const, fun v _ => ⟨le_rfl, zero_le_one⟩⟩, ?_, ?_⟩
    · intro v _; simp
    · intro v _ v' _; simp
  have : revenue M ⟨fun _ => 0, fun _ => 0⟩ = 0 := by simp [revenue]
  calc (0:ℝ) = revenue M ⟨fun _ => 0, fun _ => 0⟩ := this.symm
    _ ≤ optRev M 0 := le_csSup (bdd M hM 0) ⟨_, hmem, rfl⟩

/-- core inequality: `(1-δ)(Π(m) - ε/δ) ≤ Π⋆(M(0))`. -/
lemma core (M : Model) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε)
    (m : Mech) (hm : m ∈ Mset M ε) (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    (1 - δ) * (revenue M m - ε / δ) ≤ optRev M 0 := by
  obtain ⟨⟨hxm, htm, hx01⟩, hIR, hIC⟩ := hm
  have hvb : 0 < M.vbar := hM.1
  have hf0 := hM.2.1
  have hone := hM.2.2.2.2
  set c := 1 - δ with hc
  have hc0 : 0 < c := by simp only [hc]; linarith [hδ.2]
  have h0S : (0 : ℝ) ∈ (Icc (0:ℝ) M.vbar) := ⟨le_rfl, hvb.le⟩
  set t0 := m.t 0
  -- bounds on t over (Icc (0:ℝ) M.vbar)
  have htlo : ∀ w ∈ (Icc (0:ℝ) M.vbar), t0 - ε ≤ m.t w := by
    intro w hw; have := hIC 0 h0S w hw; simp at this; simp only [t0]; linarith
  have hthi : ∀ w ∈ (Icc (0:ℝ) M.vbar), m.t w ≤ M.vbar := by
    intro w hw
    have h1 := hIR w hw
    have h2 := hx01 w hw
    nlinarith [hw.1, hw.2, h2.1, h2.2]
  -- the closed menu
  set A : Set (ℝ × ℝ) := (fun w => (m.x w, m.t w)) '' (Icc (0:ℝ) M.vbar)
  set P : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (0:ℝ) 1 ∧ p.2 ∈ Icc (t0 - ε) M.vbar ∧
      ∀ v ∈ (Icc (0:ℝ) M.vbar), v * p.1 - p.2 - ε ≤ v * m.x v - m.t v}
  have hPc : IsClosed P := by
    have e : P = (Prod.fst ⁻¹' Icc (0:ℝ) 1) ∩ (Prod.snd ⁻¹' Icc (t0 - ε) M.vbar) ∩
        ⋂ v ∈ (Icc (0:ℝ) M.vbar), {p : ℝ × ℝ | v * p.1 - p.2 - ε ≤ v * m.x v - m.t v} := by
      ext p; simp [P, and_assoc]
    rw [e]
    refine ((isClosed_Icc.preimage continuous_fst).inter
      (isClosed_Icc.preimage continuous_snd)).inter ?_
    refine isClosed_biInter (fun v _ => ?_)
    exact isClosed_le (by fun_prop) continuous_const
  have hAP : A ⊆ P := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hx01 w hw, ⟨htlo w hw, hthi w hw⟩, fun v hv => hIC v hv w hw⟩
  set K := closure A
  have hKP : K ⊆ P := closure_minimal hAP hPc
  have hKc : IsCompact K := by
    refine (isCompact_Icc (a := ((0:ℝ), t0 - ε)) (b := ((1:ℝ), M.vbar))).of_isClosed_subset
      isClosed_closure ?_
    intro p hp
    have := hKP hp
    exact ⟨⟨this.1.1, this.2.1.1⟩, ⟨this.1.2, this.2.1.2⟩⟩
  have hKne : K.Nonempty := ⟨_, subset_closure ⟨0, h0S, rfl⟩⟩
  have hex : ∀ v : ℝ, ∃ p ∈ K, IsMaxOn (fun q : ℝ × ℝ => v * q.1 - c * q.2) K p := by
    intro v
    exact hKc.exists_isMaxOn hKne (by fun_prop)
  choose p hpK hpmax using hex
  set a : ℝ → ℝ := fun v => (p v).1
  set b : ℝ → ℝ := fun v => (p v).2
  have hmax : ∀ v, ∀ q ∈ K, v * q.1 - c * q.2 ≤ v * a v - c * b v := by
    intro v q hq; exact hpmax v hq
  have hpP : ∀ v, p v ∈ P := fun v => hKP (hpK v)
  have hopt : ∀ v ∈ (Icc (0:ℝ) M.vbar), ∀ w ∈ (Icc (0:ℝ) M.vbar), v * a w - c * b w ≤ v * a v - c * b v :=
    fun v _ w _ => hmax v (p w) (hpK w)
  have ha0 : ∀ v ∈ (Icc (0:ℝ) M.vbar), 0 ≤ a v := fun v _ => (hpP v).1.1
  obtain ⟨hma, hmb⟩ := meas_of_opt M.vbar c hvb.le a b ha0 hopt
  -- the rounded mechanism
  set mt : Mech := ⟨(Icc (0:ℝ) M.vbar).indicator a, (Icc (0:ℝ) M.vbar).indicator (fun v => c * b v)⟩
  have hmt : mt ∈ Mset M 0 := by
    refine ⟨⟨hma, hmb, fun v hv => ?_⟩, fun v hv => ?_, fun v hv v' hv' => ?_⟩
    · simp only [mt, indicator_of_mem hv]; exact (hpP v).1
    · simp only [mt, indicator_of_mem hv]
      have h1 := hmax v (m.x v, m.t v) (subset_closure ⟨v, hv, rfl⟩)
      have h2 := hIR v hv
      have h3 := (hx01 v hv).1
      simp only at h1
      have : 0 ≤ v * m.x v := mul_nonneg hv.1 h3
      have hd : 0 < δ := hδ.1
      nlinarith
    · simp only [mt, indicator_of_mem hv, indicator_of_mem hv']
      have := hmax v (p v') (hpK v')
      simp only [a, b] at this ⊢
      linarith
  -- payment loss
  have hloss : ∀ v ∈ (Icc (0:ℝ) M.vbar), m.t v - ε / δ ≤ b v := by
    intro v hv
    have h1 := (hpP v).2.2 v hv
    have h2 := hmax v (m.x v, m.t v) (subset_closure ⟨v, hv, rfl⟩)
    simp only at h2
    have hd : 0 < δ := hδ.1
    have key : δ * m.t v ≤ δ * b v + ε := by
      simp only [a, b, hc] at h1 h2 ⊢
      nlinarith
    rw [sub_le_iff_le_add]
    have e : b v + ε / δ = (δ * b v + ε) / δ := by field_simp
    rw [e, le_div_iff₀ hd]
    linarith
  -- integrability
  have hfI : IntegrableOn M.f (Icc (0:ℝ) M.vbar) := (f_integrable M hM).integrableOn
  have hbI : IntegrableOn (fun v => b v * M.f v) (Icc (0:ℝ) M.vbar) := by
    refine Integrable.bdd_mul (c := max |t0 - ε| |M.vbar|) hfI ?_ ?_
    · have : Measurable ((Icc (0:ℝ) M.vbar).indicator b) := by
        have : (Icc (0:ℝ) M.vbar).indicator b = fun v => c⁻¹ * (Icc (0:ℝ) M.vbar).indicator (fun v => c * b v) v := by
          funext v
          by_cases hv : v ∈ (Icc (0:ℝ) M.vbar)
          · simp [indicator_of_mem hv]; field_simp
          · simp [indicator_of_notMem hv]
        rw [this]; exact measurable_const.mul hmb
      refine (this.aestronglyMeasurable).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      simp [indicator_of_mem hv]
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      have := (hpP v).2.1
      exact abs_le_max_abs_abs this.1 this.2
  have htI : IntegrableOn (fun v => m.t v * M.f v) (Icc (0:ℝ) M.vbar) := by
    refine Integrable.bdd_mul (c := max |t0 - ε| |M.vbar|) hfI htm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact abs_le_max_abs_abs (htlo v hv) (hthi v hv)
  have toII : ∀ g : ℝ → ℝ, IntegrableOn g (Icc (0:ℝ) M.vbar) → IntervalIntegrable g volume 0 M.vbar :=
    fun g hg => (intervalIntegrable_iff_integrableOn_Icc_of_le hvb.le).2 hg
  have hfII := toII _ hfI
  have hbII := toII _ hbI
  have htII := toII _ htI
  -- revenue of mt
  have hrev : revenue M mt = c * ∫ v in (0)..M.vbar, b v * M.f v := by
    unfold revenue
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hvb.le] at hv
    simp only [mt, indicator_of_mem hv]; ring
  have hlow : revenue M m - ε / δ ≤ ∫ v in (0)..M.vbar, b v * M.f v := by
    have e : revenue M m - ε / δ = ∫ v in (0)..M.vbar, (m.t v - ε / δ) * M.f v := by
      unfold revenue
      have : (fun v => (m.t v - ε / δ) * M.f v) = fun v => m.t v * M.f v - ε / δ * M.f v := by
        funext v; ring
      rw [this, intervalIntegral.integral_sub htII (hfII.const_mul _),
        intervalIntegral.integral_const_mul, hone, mul_one]
    rw [e]
    apply intervalIntegral.integral_mono_on hvb.le
    · have : (fun v => (m.t v - ε / δ) * M.f v) = fun v => m.t v * M.f v - ε / δ * M.f v := by
        funext v; ring
      rw [this]; exact htII.sub (hfII.const_mul _)
    · exact hbII
    · intro v hv
      exact mul_le_mul_of_nonneg_right (hloss v hv) (hf0 v)
  calc c * (revenue M m - ε / δ) ≤ c * ∫ v in (0)..M.vbar, b v * M.f v :=
        mul_le_mul_of_nonneg_left hlow hc0.le
    _ = revenue M mt := hrev.symm
    _ ≤ optRev M 0 := le_csSup (bdd M hM 0) ⟨mt, hmt, rfl⟩

end AIC0Gap

open AIC0Gap in
theorem solution (M : ApproxIC.Rounding.Model) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε)
    (m : ApproxIC.Rounding.Mech) (hm : m ∈ ApproxIC.Rounding.Mset M ε) :
    (∀ δ ∈ Set.Ioo (0 : ℝ) 1,
      ApproxIC.Rounding.revenue M m - ApproxIC.Rounding.optRev M 0 ≤
        δ / (1 - δ) * ApproxIC.Rounding.optRev M 0 + ε / δ) ∧
    (∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2),
      ApproxIC.Rounding.revenue M m - ApproxIC.Rounding.optRev M 0 ≤
        2 * δ * ApproxIC.Rounding.optRev M 0 + ε / δ) := by
  have h1 : ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
      ApproxIC.Rounding.revenue M m - ApproxIC.Rounding.optRev M 0 ≤
        δ / (1 - δ) * ApproxIC.Rounding.optRev M 0 + ε / δ := by
    intro δ hδ
    have hc := core M hM ε hε m hm δ hδ
    have hc0 : 0 < 1 - δ := by linarith [hδ.2]
    have e : δ / (1 - δ) * ApproxIC.Rounding.optRev M 0 =
        ApproxIC.Rounding.optRev M 0 / (1 - δ) - ApproxIC.Rounding.optRev M 0 := by
      field_simp; ring
    rw [e]
    have : ApproxIC.Rounding.revenue M m - ε / δ ≤ ApproxIC.Rounding.optRev M 0 / (1 - δ) := by
      rw [le_div_iff₀ hc0]; linarith
    linarith
  refine ⟨h1, fun δ hδ => ?_⟩
  have hd1 : δ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hδ.1, by linarith [hδ.2]⟩
  have h := h1 δ hd1
  have hO := optRev_nonneg M hM
  have hc0 : 0 < 1 - δ := by linarith [hδ.2]
  have : δ / (1 - δ) ≤ 2 * δ := by
    rw [div_le_iff₀ hc0]; nlinarith [hδ.1, hδ.2]
  have := mul_le_mul_of_nonneg_right this hO
  linarith
