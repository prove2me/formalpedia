-- Prove2me | solution 1 for ApproxEquilibriumCost.General.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:11:34.332147+00:00
-- url     : https://prove2.me/submissions/9f1bdb24-2be5-4f66-aa49-a2e635ea5346

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_Parameters

section
set_option autoImplicit false

namespace ApproxEquilibriumCost.Dev.L36

noncomputable def M (a x : ℝ) : ℝ := x * (1 - (1 - x) ^ a)

lemma M_cont (a : ℝ) (ha : 0 ≤ a) : Continuous (M a) := by
  unfold M
  have : Continuous fun x : ℝ => (1 - x) ^ a :=
    (Real.continuous_rpow_const ha).comp (continuous_const.sub continuous_id)
  fun_prop

lemma M_deriv (a x : ℝ) (hx : x < 1) :
    HasDerivAt (M a) (1 - (1 - x) ^ a + a * x * (1 - x) ^ (a - 1)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have h2 := h1.rpow_const (p := a) (Or.inl (by linarith : (1 - x) ≠ 0))
  have h3 := (hasDerivAt_id x).mul (h2.const_sub 1)
  unfold M
  refine h3.congr_deriv ?_
  simp only [id]
  ring

lemma m_deriv (a x : ℝ) (hx : x < 1) :
    HasDerivAt (fun y : ℝ => 1 - (1 - y) ^ a + a * y * (1 - y) ^ (a - 1))
      (2 * a * (1 - x) ^ (a - 1) - a * (a - 1) * x * (1 - x) ^ (a - 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have hne : (1 - x) ≠ 0 := by linarith
  have h2 := h1.rpow_const (p := a) (Or.inl hne)
  have h2' := h1.rpow_const (p := a - 1) (Or.inl hne)
  have h3 := (h2.const_sub 1).add (((hasDerivAt_id x).const_mul a).mul h2')
  refine h3.congr_deriv ?_
  have : a - 1 - 1 = a - 2 := by ring
  simp only [id, this]
  ring

lemma m_mono (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    MonotoneOn (fun y : ℝ => 1 - (1 - y) ^ a + a * y * (1 - y) ^ (a - 1)) (Set.Ioo 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
  · intro x hx
    exact (m_deriv a x hx.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    exact (m_deriv a x hx.2).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(m_deriv a x hx.2).deriv]
    have hu : 0 < 1 - x := by linarith [hx.2]
    have e1 : 0 < (1 - x) ^ (a - 1) := Real.rpow_pos_of_pos hu _
    have e2 : 0 < (1 - x) ^ (a - 2) := Real.rpow_pos_of_pos hu _
    have : 0 ≤ -(a * (a - 1) * x) * (1 - x) ^ (a - 2) := by
      apply mul_nonneg _ e2.le
      have : 0 ≤ a * (1 - a) * x := by
        apply mul_nonneg (mul_nonneg ha.le (by linarith)) hx.1.le
      linarith
    nlinarith [mul_pos ha e1]


lemma F_deriv (a x : ℝ) (hx : x < 1) :
    HasDerivAt (fun y : ℝ => 1 - y + M a y)
      (-((1 - x) ^ (a - 1) * (1 - (1 + a) * x))) x := by
  have h := ((hasDerivAt_id x).const_sub 1).add (M_deriv a x hx)
  refine h.congr_deriv ?_
  have hu : (1 - x) ^ a = (1 - x) ^ (a - 1) * (1 - x) := by
    have := Real.rpow_add_one (by linarith : (1 - x) ≠ 0) (a - 1)
    rwa [sub_add_cancel] at this
  rw [hu]
  ring

end ApproxEquilibriumCost.Dev.L36

namespace ApproxEquilibriumCost.General

theorem chk_lemma_3_6 (d : ℕ) (hd : 1 ≤ d) :
    ContinuousOn (mu d) (Set.Icc 0 1) ∧
    StrictMonoOn (mu d) (Set.Icc 0 1) ∧
    ConvexOn ℝ (Set.Icc 0 1) (mu d) ∧
    mu d '' Set.Icc 0 1 = Set.Icc 0 1 ∧
    AntitoneOn (fun x => 1 - x + mu d x) (Set.Icc 0 (criticalPoint d)) ∧
    MonotoneOn (fun x => 1 - x + mu d x) (Set.Icc (criticalPoint d) 1) ∧
    criticalPoint d ∈ Set.Icc (0 : ℝ) 1 ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      1 - criticalPoint d + mu d (criticalPoint d) ≤ 1 - x + mu d x) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      1 - x + mu d x = 1 - criticalPoint d + mu d (criticalPoint d) →
        x = criticalPoint d) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set a : ℝ := 1 / (d : ℝ) with ha_def
  have ha : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha_def, div_le_one hdpos]; exact hd1
  have hmu : mu d = ApproxEquilibriumCost.Dev.L36.M a := rfl
  have hc : criticalPoint d = 1 / (1 + a) := by
    unfold criticalPoint; rw [ha_def]; field_simp
  have hc0 : 0 < criticalPoint d := by unfold criticalPoint; positivity
  have hc1 : criticalPoint d < 1 := by
    unfold criticalPoint; rw [div_lt_one (by positivity)]; linarith
  have hcont : ContinuousOn (mu d) (Set.Icc 0 1) := by
    rw [hmu]; exact (ApproxEquilibriumCost.Dev.L36.M_cont a ha.le).continuousOn
  have hsm : StrictMonoOn (mu d) (Set.Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont
    intro x hx
    rw [interior_Icc] at hx
    rw [hmu, (ApproxEquilibriumCost.Dev.L36.M_deriv a x hx.2).deriv]
    have h1 : (1 - x) ^ a < 1 :=
      Real.rpow_lt_one (by linarith [hx.2]) (by linarith [hx.1]) ha
    have h2 : 0 < (1 - x) ^ (a - 1) := Real.rpow_pos_of_pos (by linarith [hx.2]) _
    have := mul_pos (mul_pos ha hx.1) h2
    linarith
  have hconv : ConvexOn ℝ (Set.Icc 0 1) (mu d) := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1) hcont
    · intro x hx
      rw [interior_Icc] at hx
      rw [hmu]
      exact (ApproxEquilibriumCost.Dev.L36.M_deriv a x hx.2).differentiableAt.differentiableWithinAt
    · intro x hx y hy hxy
      rw [interior_Icc] at hx hy
      rw [hmu, (ApproxEquilibriumCost.Dev.L36.M_deriv a x hx.2).deriv,
        (ApproxEquilibriumCost.Dev.L36.M_deriv a y hy.2).deriv]
      have := ApproxEquilibriumCost.Dev.L36.m_mono a ha ha1 hx hy hxy
      simpa [mul_assoc] using this
  have hM0 : mu d 0 = 0 := by simp [hmu, ApproxEquilibriumCost.Dev.L36.M]
  have hM1 : mu d 1 = 1 := by
    simp [hmu, ApproxEquilibriumCost.Dev.L36.M, Real.zero_rpow ha.ne']
  have himg : mu d '' Set.Icc 0 1 = Set.Icc 0 1 := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      constructor
      · rw [← hM0]; exact hsm.monotoneOn (by simp) hx hx.1
      · rw [← hM1]; exact hsm.monotoneOn hx (by simp) hx.2
    · have := intermediate_value_Icc (zero_le_one' ℝ) hcont
      rwa [hM0, hM1] at this
  have hFc : ContinuousOn (fun x => 1 - x + mu d x) (Set.Icc 0 1) :=
    (continuousOn_const.sub continuousOn_id).add hcont
  have hFd : ∀ x, x < 1 → HasDerivAt (fun y : ℝ => 1 - y + mu d y)
      (-((1 - x) ^ (a - 1) * (1 - (1 + a) * x))) x := fun x hx =>
    ApproxEquilibriumCost.Dev.L36.F_deriv a x hx
  have hanti : StrictAntiOn (fun x => 1 - x + mu d x) (Set.Icc 0 (criticalPoint d)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · exact hFc.mono (Set.Icc_subset_Icc_right hc1.le)
    · intro x hx
      rw [interior_Icc] at hx
      have hx1 : x < 1 := by linarith [hx.2]
      rw [(hFd x hx1).deriv]
      have h2 : 0 < (1 - x) ^ (a - 1) := Real.rpow_pos_of_pos (by linarith) _
      have h3 : 0 < 1 - (1 + a) * x := by
        have := hx.2
        rw [hc, lt_div_iff₀ (by linarith)] at this
        linarith
      have := mul_pos h2 h3
      linarith
  have hmono : StrictMonoOn (fun x => 1 - x + mu d x) (Set.Icc (criticalPoint d) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact hFc.mono (Set.Icc_subset_Icc_left hc0.le)
    · intro x hx
      rw [interior_Icc] at hx
      have hx1 : x < 1 := hx.2
      rw [(hFd x hx1).deriv]
      have h2 : 0 < (1 - x) ^ (a - 1) := Real.rpow_pos_of_pos (by linarith) _
      have h3 : 0 < (1 + a) * x - 1 := by
        have := hx.1
        rw [hc, div_lt_iff₀ (by linarith)] at this
        linarith
      have := mul_pos h2 h3
      linarith
  have hcI : criticalPoint d ∈ Set.Icc (0 : ℝ) 1 := ⟨hc0.le, hc1.le⟩
  refine ⟨hcont, hsm, hconv, himg, hanti.antitoneOn, hmono.monotoneOn, hcI, ?_, ?_⟩
  · intro x hx
    rcases le_total x (criticalPoint d) with h | h
    · exact hanti.antitoneOn ⟨hx.1, h⟩ ⟨hc0.le, le_rfl⟩ h
    · exact hmono.monotoneOn ⟨le_rfl, hc1.le⟩ ⟨h, hx.2⟩ h
  · intro x hx heq
    rcases lt_trichotomy x (criticalPoint d) with h | h | h
    · have := hanti ⟨hx.1, h.le⟩ ⟨hc0.le, le_rfl⟩ h
      simp only at this
      linarith
    · exact h
    · have := hmono ⟨le_rfl, hc1.le⟩ ⟨h.le, hx.2⟩ h
      simp only at this
      linarith

end ApproxEquilibriumCost.General
end

theorem solution : type_of% @ApproxEquilibriumCost.General.chk_lemma_3_6 := @ApproxEquilibriumCost.General.chk_lemma_3_6
