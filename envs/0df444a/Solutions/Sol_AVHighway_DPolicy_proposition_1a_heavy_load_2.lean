-- Prove2me | solution 2 for AVHighway.DPolicy.proposition_1a_heavy_load
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:36.994232+00:00
-- url     : https://prove2.me/submissions/d6fa48d6-a088-4b1b-a23d-8ec8d841fe8d

import Mathlib
import Definitions.Def_AVHighway_DPolicy_Setting
import Theorems.Thm_AVHighway_DPolicy_limit_comparison
import Theorems.Thm_AVHighway_DPolicy_heavy_traffic_limits_policies

-- carved verbatim out of submission f919601f-ad41-4f7b-8deb-c49833095cfc, lines 234-278

section
set_option autoImplicit false
open AVHighway.DPolicy

theorem avh_lc_lt (N c : ℕ) (L : ℝ) (hL : 0 < L) (VB VDA VDH : ℕ → ℝ)
    (hVBjam : 0 < VB (N * c)) (hVDAjam : 0 < VDA c) (hVDHjam : 0 < VDH ((N - 1) * c))
    (hAV : VDH ((N - 1) * c) < VDA c) (p : ℝ) :
    p * L / VDA c + (1 - p) * L / VDH ((N - 1) * c) < L / VB (N * c) ↔
      pDW N c VB VDA VDH < p := by
  unfold pDW
  generalize VDA c = a at *
  generalize VDH ((N - 1) * c) = h at *
  generalize VB (N * c) = b at *
  have hden : 0 < a * b - b * h := by nlinarith [mul_pos hVBjam (sub_pos.2 hAV)]
  rw [div_lt_iff₀ hden, div_add_div _ _ hVDAjam.ne' hVDHjam.ne',
    div_lt_div_iff₀ (mul_pos hVDAjam hVDHjam) hVBjam]
  have e : L * (a * h) - (p * L * h + a * ((1 - p) * L)) * b
      = L * ((a * b - b * h) * p - (a * b - a * h)) := by ring
  constructor
  · intro H
    have h1 : 0 < L * ((a * b - b * h) * p - (a * b - a * h)) := by rw [← e]; linarith
    have h2 := (mul_pos_iff_of_pos_left hL).1 h1
    linarith
  · intro H
    have h1 : 0 < L * ((a * b - b * h) * p - (a * b - a * h)) :=
      mul_pos hL (by linarith)
    rw [← e] at h1
    linarith

theorem solution (N c : ℕ) (hN : 2 ≤ N) (hc : 1 ≤ c) (L : ℝ) (hL : 0 < L)
    (VB VDA VDH : ℕ → ℝ)
    (hVB : ∀ n, 1 ≤ n → n ≤ N * c → 0 < VB n) (hVB_anti : AntitoneOn VB (Set.Icc 1 (N * c)))
    (hVDA : ∀ n, 1 ≤ n → n ≤ c → 0 < VDA n) (hVDA_anti : AntitoneOn VDA (Set.Icc 1 c))
    (hVDH : ∀ n, 1 ≤ n → n ≤ (N - 1) * c → 0 < VDH n)
    (hVDH_anti : AntitoneOn VDH (Set.Icc 1 ((N - 1) * c)))
    (hjam : VDH ((N - 1) * c) < VB (N * c))
    (hAV : VDH ((N - 1) * c) < VDA c)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hp_ne : p ≠ pDW N c VB VDA VDH) :
    ∃ lamBar : ℝ, 0 < lamBar ∧ ∀ lam ≥ lamBar,
      (dPolicyW L N c VDA VDH p lam ≤ benchmarkW L N c VB lam ↔ pDW N c VB VDA VDH ≤ p) := by
  have hNc : 1 ≤ N * c := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hN1c : 1 ≤ (N - 1) * c := Nat.one_le_iff_ne_zero.2 (by
    have : 1 ≤ N - 1 := by omega
    positivity)
  obtain ⟨hB, hD⟩ := AVHighway.DPolicy.heavy_traffic_limits_policies N c hN hc L hL VB VDA VDH hVB hVDA hVDH p hp
  have hb := hVB (N * c) hNc le_rfl
  have ha := hVDA c hc le_rfl
  have hh := hVDH ((N - 1) * c) hN1c le_rfl
  have hlc := AVHighway.DPolicy.limit_comparison N c L hL VB VDA VDH hb ha hh hAV p
  set WB := L / VB (N * c)
  set WD := p * L / VDA c + (1 - p) * L / VDH ((N - 1) * c)
  have hev : ∀ᶠ lam : ℝ in Filter.atTop,
      (dPolicyW L N c VDA VDH p lam ≤ benchmarkW L N c VB lam ↔ pDW N c VB VDA VDH ≤ p) := by
    rcases lt_or_gt_of_ne hp_ne with hlt | hgt
    · have hn : ¬ WD ≤ WB := fun h => absurd (hlc.1 h) (not_le.2 hlt)
      have hgt' : WB < WD := not_le.1 hn
      have hm1 : WB < (WB + WD) / 2 := by linarith
      have hm2 : (WB + WD) / 2 < WD := by linarith
      filter_upwards [hB.eventually (gt_mem_nhds hm1), hD.eventually (lt_mem_nhds hm2)]
        with lam h1 h2
      constructor
      · intro h; linarith
      · intro h; exact absurd h (not_le.2 hlt)
    · have hlt' : WD < WB := (avh_lc_lt N c L hL VB VDA VDH hb ha hh hAV p).2 hgt
      have hm1 : WD < (WB + WD) / 2 := by linarith
      have hm2 : (WB + WD) / 2 < WB := by linarith
      filter_upwards [hD.eventually (gt_mem_nhds hm1), hB.eventually (lt_mem_nhds hm2)]
        with lam h1 h2
      constructor
      · intro h; exact hgt.le
      · intro h; linarith
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hev
  exact ⟨max T 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun lam hl => hT lam (le_trans (le_max_left _ _) hl)⟩

end
