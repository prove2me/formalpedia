-- Prove2me | solution 1 for ApproxEquilibriumCost.General.rho_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:11:33.884063+00:00
-- url     : https://prove2.me/submissions/46f58053-107c-465a-a985-0ffcd4ffffb4

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_Parameters
import Theorems.Thm_ApproxEquilibriumCost_General_lemma_3_6

section
set_option autoImplicit false

namespace ApproxEquilibriumCost.General

theorem chk_rho_spec (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) :
    rho d ε ∈ Set.Ico (0 : ℝ) 1 ∧
    mu d (rho d ε) = ε * (1 - rho d ε) ∧
    (∀ x ∈ Set.Ico (0 : ℝ) 1, mu d x = ε * (1 - x) → x = rho d ε) := by
  obtain ⟨hcont, hsm, -, -⟩ := lemma_3_6 d hd
  set g : ℝ → ℝ := fun x => mu d x - ε * (1 - x) with hg
  have gcont : ContinuousOn g (Set.Icc 0 1) :=
    hcont.sub ((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)))
  have gsm : StrictMonoOn g (Set.Icc 0 1) := by
    intro x hx y hy hxy
    have := hsm hx hy hxy
    simp only [hg]
    nlinarith
  have hmu0 : mu d 0 = 0 := by simp [mu]
  have hmu1 : mu d 1 = 1 := by
    have : (d : ℝ) ≠ 0 := by positivity
    simp [mu, Real.zero_rpow (inv_ne_zero this)]
  have g0 : g 0 ≤ 0 := by simp [hg, hmu0, hε]
  have g1 : g 1 = 1 := by simp [hg, hmu1]
  obtain ⟨r, hr, hgr⟩ : ∃ r ∈ Set.Icc (0:ℝ) 1, g r = 0 := by
    have := intermediate_value_Icc (zero_le_one' ℝ) gcont
    exact this ⟨g0, by rw [g1]; exact zero_le_one⟩
  have hr1 : r < 1 := by
    rcases hr.2.lt_or_eq with h | h
    · exact h
    · rw [h, g1] at hgr; exact absurd hgr one_ne_zero
  have hrho : rho d ε = r := by
    unfold rho
    rw [if_pos ⟨hd, hε⟩]
    apply IsLeast.csInf_eq
    refine ⟨⟨hr, ?_⟩, ?_⟩
    · have : mu d r - ε * (1 - r) = 0 := hgr
      linarith
    · rintro x ⟨hx, hxs⟩
      by_contra hlt
      push Not at hlt
      have := gsm hx hr hlt
      simp only [hg] at this hgr
      linarith
  rw [hrho]
  refine ⟨⟨hr.1, hr1⟩, by simp only [hg] at hgr; linarith, ?_⟩
  intro x hx hxe
  have : g x = g r := by simp only [hg] at hgr ⊢; linarith
  exact gsm.injOn ⟨hx.1, hx.2.le⟩ hr this

end ApproxEquilibriumCost.General
end

theorem solution : type_of% @ApproxEquilibriumCost.General.chk_rho_spec := @ApproxEquilibriumCost.General.chk_rho_spec
