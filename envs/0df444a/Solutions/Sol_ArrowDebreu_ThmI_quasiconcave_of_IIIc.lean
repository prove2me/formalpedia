-- Prove2me | solution 1 for ArrowDebreu.ThmI.quasiconcave_of_IIIc
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:10:04.323034+00:00
-- url     : https://prove2.me/submissions/6adffd29-eb5e-423a-ae30-ead01ac465af

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- The equal-utility case of the quasi-concavity argument. -/
theorem aux_qcIIIc_eq {l : ℕ} (X : Set (Fin l → ℝ)) (u : (Fin l → ℝ) → ℝ)
    (hconv : Convex ℝ X) (hcont : ContinuousOn u X)
    (H : ∀ x ∈ X, ∀ x' ∈ X, u x' < u x →
      ∀ t : ℝ, 0 < t → t < 1 → u x' < u (t • x + (1 - t) • x'))
    {x y : Fin l → ℝ} (hx : x ∈ X) (hy : y ∈ X) (hxy : u x = u y)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    u y ≤ u (t • x + (1 - t) • y) := by
  by_contra hlt
  rw [not_le] at hlt
  set g : ℝ → ℝ := fun s => u (s • x + (1 - s) • y) with hg
  have hmem : ∀ s ∈ Set.Icc (0:ℝ) 1, s • x + (1 - s) • y ∈ X := by
    intro s hs
    exact hconv hx hy hs.1 (by linarith [hs.2]) (by ring)
  have hgcont : ContinuousOn g (Set.Icc t 1) := by
    have h1 : ContinuousOn (fun s : ℝ => s • x + (1 - s) • y) (Set.Icc t 1) := by
      fun_prop
    refine hcont.comp h1 ?_
    intro s hs
    exact hmem s ⟨by linarith [hs.1], hs.2⟩
  have hgt : g t < u y := hlt
  have hg1 : g 1 = u y := by
    simp [hg, hxy]
  set v : ℝ := (g t + u y) / 2 with hv
  have hvmem : v ∈ Set.Icc (g t) (g 1) := by
    rw [hg1]; constructor <;> linarith
  obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc ht1.le hgcont hvmem
  have hst : t < s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · exfalso; rw [← h] at hgs; linarith
    · exact h
  have hs0 : 0 < s := lt_trans ht0 hst
  set w : Fin l → ℝ := s • x + (1 - s) • y with hw
  have hwX : w ∈ X := hmem s ⟨hs0.le, hs.2⟩
  have huw : u w = v := hgs
  have huwy : u w < u y := by rw [huw]; linarith
  have key := H y hy w hwX huwy (1 - t / s)
    (by rw [sub_pos, div_lt_one hs0]; exact hst)
    (by have : 0 < t / s := div_pos ht0 hs0; linarith)
  have heq : (1 - t / s) • y + (1 - (1 - t / s)) • w = t • x + (1 - t) • y := by
    rw [hw]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [heq] at key
  have : u (t • x + (1 - t) • y) = g t := rfl
  linarith

end ArrowDebreu.ThmI

open ArrowDebreu.ThmI
open ArrowDebreu.Shared

theorem solution {l m n : ℕ} (E : Economy l m n) (hII : AssumptionII E)
    (hIIIa : AssumptionIIIa E) (hIIIc : AssumptionIIIc E) :
    ∀ i, QuasiconcaveOn ℝ (E.X i) (E.u i) := by
  intro i
  have hconv : Convex ℝ (E.X i) := (hII i).2.1
  have H := hIIIc i
  refine quasiconcaveOn_iff_min_le.2 ⟨hconv, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0; simp
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · have : a = 1 := by linarith
    subst this; simp
  have ha1 : a < 1 := by linarith
  rcases lt_trichotomy (E.u i x) (E.u i y) with h | h | h
  · have := H y hy x hx h (1 - a) hb0 (by linarith)
    have e : (1 - a) • y + (1 - (1 - a)) • x = a • x + (1 - a) • y := by
      rw [sub_sub_cancel, add_comm]
    rw [e] at this
    exact le_trans (min_le_left _ _) this.le
  · exact le_trans (min_le_right _ _)
      (aux_qcIIIc_eq (E.X i) (E.u i) hconv (hIIIa i) H hx hy h ha0 ha1)
  · have := H x hx y hy h a ha0 ha1
    exact le_trans (min_le_right _ _) this.le
