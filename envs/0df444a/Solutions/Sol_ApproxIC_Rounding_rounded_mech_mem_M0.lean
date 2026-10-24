-- Prove2me | solution 1 for ApproxIC.Rounding.rounded_mech_mem_M0
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:47:35.24106+00:00
-- url     : https://prove2.me/submissions/d4699bda-aa33-4839-9831-3a83692cfe4f

import Mathlib
import Definitions.Def_ApproxIC_Rounding_Setting

open MeasureTheory Set ApproxIC.Rounding

namespace AIC0M0

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

end AIC0M0

open AIC0M0 in
theorem solution (M : ApproxIC.Rounding.Model) (hM : M.Standing) (ε δ : ℝ) (m : ApproxIC.Rounding.Mech)
    (hm : m ∈ ApproxIC.Rounding.Mset M ε) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (vs : ℝ → ℝ)
    (hvs : ∀ v ∈ Set.Icc 0 M.vbar, vs v ∈ Set.Icc 0 M.vbar ∧
      ∀ w ∈ Set.Icc 0 M.vbar, v * m.x w - (1 - δ) * m.t w ≤ v * m.x (vs v) - (1 - δ) * m.t (vs v)) :
    (⟨(Set.Icc 0 M.vbar).indicator (fun v => m.x (vs v)),
      (Set.Icc 0 M.vbar).indicator (fun v => (1 - δ) * m.t (vs v))⟩ : ApproxIC.Rounding.Mech) ∈
        ApproxIC.Rounding.Mset M 0 := by
  obtain ⟨⟨_, _, hx01⟩, hIR, _⟩ := hm
  have hvb : 0 < M.vbar := hM.1
  have hopt : ∀ v ∈ Icc 0 M.vbar, ∀ w ∈ Icc 0 M.vbar,
      v * m.x (vs w) - (1 - δ) * m.t (vs w) ≤ v * m.x (vs v) - (1 - δ) * m.t (vs v) :=
    fun v hv w hw => (hvs v hv).2 (vs w) (hvs w hw).1
  have ha0 : ∀ v ∈ Icc 0 M.vbar, 0 ≤ m.x (vs v) := fun v hv => (hx01 _ (hvs v hv).1).1
  obtain ⟨hma, hmb⟩ := meas_of_opt M.vbar (1 - δ) hvb.le (fun v => m.x (vs v))
    (fun v => m.t (vs v)) ha0 hopt
  refine ⟨⟨hma, hmb, fun v hv => ?_⟩, fun v hv => ?_, fun v hv v' hv' => ?_⟩
  · simp only [indicator_of_mem hv]; exact hx01 _ (hvs v hv).1
  · simp only [indicator_of_mem hv]
    have h1 := (hvs v hv).2 v hv
    have h2 := hIR v hv
    have h3 := (hx01 v hv).1
    have : 0 ≤ v * m.x v := mul_nonneg hv.1 h3
    have hd : 0 < δ := hδ.1
    nlinarith [mul_nonneg (sub_nonneg.2 hδ.2.le) h2, mul_nonneg hd.le this]
  · simp only [indicator_of_mem hv, indicator_of_mem hv']
    have := hopt v hv v' hv'
    linarith
