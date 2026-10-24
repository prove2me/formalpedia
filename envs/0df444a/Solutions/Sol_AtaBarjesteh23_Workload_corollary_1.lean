-- Prove2me | solution 1 for AtaBarjesteh23.Workload.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:03:38.204562+00:00
-- url     : https://prove2.me/submissions/da731439-7aab-4c93-99a5-1bc52f4ceb1a

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control
import Theorems.Thm_AtaBarjesteh23_Workload_lemma_4_i
import Theorems.Thm_AtaBarjesteh23_Workload_lemma_4_ii
import Theorems.Thm_AtaBarjesteh23_Workload_riccati_wellposed

open MeasureTheory Set Filter Topology

open AtaBarjesteh23.Workload in
theorem solution (M : Model) (hM : M.Standing) :
    ∃! γ : ℝ, γ ∈ M.GammaMinus ∧ γ ∈ M.GammaPlus ∧ M.vMinus γ 0 = M.vPlus γ 0 := by
  obtain ⟨gc, gm, g0, gub⟩ := lemma_4_i M hM
  obtain ⟨kc, km, k0, klb⟩ := lemma_4_ii M hM
  obtain ⟨-, -, h0m, h0p, hocm, hocp⟩ := riccati_wellposed M hM
  set g := fun γ => M.vMinus γ 0 with hg
  set k := fun γ => M.vPlus γ 0 with hk
  -- a point of `Γ⁻` where `g > 0` and a point of `Γ⁺` where `k < g 0`
  obtain ⟨x, hx, hgx⟩ : ∃ x ∈ M.GammaMinus, 0 < g x := by
    by_contra h
    push_neg at h
    exact gub ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact h x hx⟩
  obtain ⟨y, hy, hky⟩ : ∃ y ∈ M.GammaPlus, k y < g 0 := by
    by_contra h
    push_neg at h
    exact klb ⟨g 0, by rintro _ ⟨y, hy, rfl⟩; exact h y hy⟩
  have hx0 : 0 ≤ x := hx.1
  have hy0 : 0 ≤ y := hy.1
  set z := min x y with hz
  have hzm : Icc 0 z ⊆ M.GammaMinus :=
    (Icc_subset_Icc_right (min_le_left x y)).trans (hocm.out h0m hx)
  have hzp : Icc 0 z ⊆ M.GammaPlus :=
    (Icc_subset_Icc_right (min_le_right x y)).trans (hocp.out h0p hy)
  have hz0 : 0 ≤ z := le_min hx0 hy0
  have hzI : z ∈ Icc (0 : ℝ) z := ⟨hz0, le_rfl⟩
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) z := ⟨le_rfl, hz0⟩
  have hdz : 0 < g z - k z := by
    rcases min_choice x y with h | h
    · rw [← hz] at h
      have : k z ≤ k 0 := km.antitoneOn (hzp h0I) (hzp hzI) hz0
      rw [h] at this ⊢
      simp only [k] at k0 this
      simp only [k]
      linarith
    · rw [← hz] at h
      have : g 0 ≤ g z := gm.monotoneOn (hzm h0I) (hzm hzI) hz0
      rw [h] at this ⊢
      linarith
  have hd0 : g 0 - k 0 < 0 := by simp only [g, k] at g0 ⊢; rw [k0]; linarith
  have hcont : ContinuousOn (fun γ => g γ - k γ) (Icc 0 z) :=
    (gc.mono hzm).sub (kc.mono hzp)
  obtain ⟨γ, hγI, hγ⟩ := intermediate_value_Icc hz0 hcont ⟨hd0.le, hdz.le⟩
  refine ⟨γ, ⟨hzm hγI, hzp hγI, ?_⟩, ?_⟩
  · have : g γ - k γ = 0 := hγ
    simp only [g, k] at this
    linarith
  · rintro γ' ⟨hm', hp', he'⟩
    have hd' : g γ' - k γ' = 0 := by simp only [g, k]; rw [he']; ring
    have hdγ : g γ - k γ = 0 := hγ
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := gm (hm') (hzm hγI) h
      have := km (hp') (hzp hγI) h
      linarith
    · have := gm (hzm hγI) (hm') h
      have := km (hzp hγI) (hp') h
      linarith
