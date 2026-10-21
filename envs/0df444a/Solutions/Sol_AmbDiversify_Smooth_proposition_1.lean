-- Prove2me | solution 1 for AmbDiversify.Smooth.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:01:49.259548+00:00
-- url     : https://prove2.me/submissions/ceb635af-9acd-41bd-b5aa-4b10ddaada67

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

set_option autoImplicit false
open AmbDiversify.Smooth

theorem vd_eq (u : ℝ → ℝ) (W0 L p : ℝ) :
    VD_risk u W0 L p = p * (1 - p) * (2 * u (W0 - L / 2) - u (W0 - L) - u W0) := by
  unfold VD_risk EU_D EU_ND
  ring

theorem solution (u : ℝ → ℝ) (hu_cont : Continuous u) :
    (∀ W0 L p : ℝ, 0 < L → 0 ≤ p → p ≤ 1 → 0 ≤ VD_risk u W0 L p) ↔
      ConcaveOn ℝ Set.univ u := by
  constructor
  · intro h
    have mid : ∀ a b : ℝ, a < b → (u a + u b) / 2 ≤ u ((a + b) / 2) := by
      intro a b hab
      have := h b (b - a) (1 / 2) (by linarith) (by norm_num) (by norm_num)
      rw [vd_eq] at this
      have e1 : b - (b - a) = a := by ring
      have e2 : b - (b - a) / 2 = (a + b) / 2 := by ring
      rw [e1, e2] at this
      linarith
    have mid' : ∀ a b : ℝ, (u a + u b) / 2 ≤ u ((a + b) / 2) := by
      intro a b
      rcases lt_trichotomy a b with hab | hab | hab
      · exact mid a b hab
      · subst hab
        have : (a + a) / 2 = a := by ring
        rw [this]; linarith
      · have := mid b a hab
        rw [add_comm b a, add_comm (u b)] at this
        exact this
    have claim : ∀ x y t : ℝ, 0 ≤ t → t ≤ 1 →
        (1 - t) * u x + t * u y ≤ u (x + t * (y - x)) := by
      intro x y
      obtain ⟨v, hv⟩ : ∃ v : ℝ → ℝ, v = fun t => u (x + t * (y - x)) - ((1 - t) * u x + t * u y) :=
        ⟨_, rfl⟩
      have hvc : Continuous v := by
        rw [hv]
        exact (hu_cont.comp (by fun_prop)).sub (by fun_prop)
      have hv0 : v 0 = 0 := by rw [hv]; simp
      have hv1 : v 1 = 0 := by
        rw [hv]
        have : x + 1 * (y - x) = y := by ring
        simp only [this]; ring
      have hvm : ∀ s r, (v s + v r) / 2 ≤ v ((s + r) / 2) := by
        intro s r
        have := mid' (x + s * (y - x)) (x + r * (y - x))
        have e : (x + s * (y - x) + (x + r * (y - x))) / 2 = x + (s + r) / 2 * (y - x) := by ring
        rw [e] at this
        rw [hv]
        simp only
        linarith
      have hnn : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ v t := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨t0, ht0, ht1, hneg⟩ := hcon
        obtain ⟨m0, hm0, hmin⟩ := isCompact_Icc.exists_isMinOn
          (Set.nonempty_Icc.2 (zero_le_one' ℝ)) hvc.continuousOn
        have hmle : v m0 ≤ v t0 := isMinOn_iff.1 hmin t0 ⟨ht0, ht1⟩
        have hS : IsCompact (Set.Icc (0 : ℝ) 1 ∩ {t | v t = v m0}) :=
          isCompact_Icc.inter_right (isClosed_eq hvc continuous_const)
        obtain ⟨s, hsS, hsmin⟩ := hS.exists_isMinOn ⟨m0, hm0, rfl⟩ continuous_id.continuousOn
        have hs01 := hsS.1
        have hsv : v s = v m0 := hsS.2
        have hs0 : s ≠ 0 := by
          intro h0; rw [h0, hv0] at hsv; linarith
        have hs1 : s ≠ 1 := by
          intro h1; rw [h1, hv1] at hsv; linarith
        have hs0' : 0 < s := lt_of_le_of_ne hs01.1 (Ne.symm hs0)
        have hs1' : s < 1 := lt_of_le_of_ne hs01.2 hs1
        obtain ⟨δ, hδ⟩ : ∃ δ, δ = min s (1 - s) := ⟨_, rfl⟩
        have hδ0 : 0 < δ := by rw [hδ]; exact lt_min hs0' (by linarith)
        have hδs : δ ≤ s := by rw [hδ]; exact min_le_left _ _
        have hδ1 : δ ≤ 1 - s := by rw [hδ]; exact min_le_right _ _
        have hA : v m0 ≤ v (s - δ) := isMinOn_iff.1 hmin (s - δ) ⟨by linarith, by linarith⟩
        have hB : v m0 ≤ v (s + δ) := isMinOn_iff.1 hmin (s + δ) ⟨by linarith, by linarith⟩
        have hA' : v m0 < v (s - δ) := by
          rcases eq_or_lt_of_le hA with h | h
          · exfalso
            have hmem : s - δ ∈ Set.Icc (0 : ℝ) 1 ∩ {t | v t = v m0} :=
              ⟨⟨by linarith, by linarith⟩, h.symm⟩
            have := isMinOn_iff.1 hsmin (s - δ) hmem
            simp only [id] at this
            linarith
          · exact h
        have := hvm (s - δ) (s + δ)
        have e : (s - δ + (s + δ)) / 2 = s := by ring
        rw [e] at this
        linarith
      intro t ht0 ht1
      have := hnn t ht0 ht1
      rw [hv] at this
      simp only at this
      linarith
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hb1 : b ≤ 1 := by linarith
    have := claim x y b hb hb1
    have ha' : a = 1 - b := by linarith
    subst ha'
    simp only [smul_eq_mul]
    have e : (1 - b) * x + b * y = x + b * (y - x) := by ring
    rw [e]
    exact this
  · intro hc W0 L p hL hp0 hp1
    rw [vd_eq]
    have hmid : (W0 - L / 2) = (1 / 2 : ℝ) • (W0 - L) + (1 / 2 : ℝ) • W0 := by
      simp only [smul_eq_mul]; ring
    have hG : 0 ≤ 2 * u (W0 - L / 2) - u (W0 - L) - u W0 := by
      have := @hc.2 (W0 - L) (Set.mem_univ _) W0 (Set.mem_univ _) (1 / 2) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num)
      rw [← hmid] at this
      simp only [smul_eq_mul] at this
      linarith
    exact mul_nonneg (mul_nonneg hp0 (by linarith)) hG
