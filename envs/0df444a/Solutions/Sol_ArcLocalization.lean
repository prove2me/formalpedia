-- Prove2me | solution 1 for ArcLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:51.992553+00:00
-- url     : https://prove2.me/submissions/2bf2c3f5-29d7-4fb5-bab2-27604e3f7f6a

import Definitions.Def_Tablet_dGamma
import Definitions.Def_Tablet_ArcLocalization

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (u ρ : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) γ.len) (hρ : 0 < ρ) (hlen : 2 * ρ < γ.len) :
    (∃ t t' : ℝ, 0 ≤ t ∧ t ≤ t' ∧ t' ≤ γ.len ∧ t' - t ≤ 2 * ρ ∧
        { v ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ u v < ρ } ⊆ Set.Icc t t' ∧
        (t = 0 ∨ dGamma γ u t = ρ) ∧ (t' = γ.len ∨ dGamma γ u t' = ρ)) ∨
      (IsClosedCurve γ ∧ ∃ t t' : ℝ, 0 ≤ t' ∧ t' < t ∧ t ≤ γ.len ∧
        (γ.len - t) + t' ≤ 2 * ρ ∧
        { v ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ u v < ρ } ⊆
          Set.Icc t γ.len ∪ Set.Icc 0 t' ∧
        dGamma γ u t = ρ ∧ dGamma γ u t' = ρ) := by
-- BODY
  obtain ⟨hu0, hul⟩ := hu
  by_cases hc : IsClosedCurve γ
  · -- `γ` is closed: `d_γ(u,v) = min |u-v| (γ.len - |u-v|)`.
    -- The two `min`-computations used for the free endpoints, at circle distance `ρ` and `l-ρ`.
    have hd : ∀ w : ℝ, dGamma γ u w = min |u - w| (γ.len - |u - w|) := by
      intro w; simp only [dGamma, if_pos hc]
    have habs1 : ∀ w : ℝ, |u - w| = ρ → dGamma γ u w = ρ := by
      intro w hw
      rw [hd w, hw, min_eq_left (by linarith : ρ ≤ γ.len - ρ)]
    have habs2 : ∀ w : ℝ, |u - w| = γ.len - ρ → dGamma γ u w = ρ := by
      intro w hw
      rw [hd w, hw, show γ.len - (γ.len - ρ) = ρ by ring,
        min_eq_right (by linarith : ρ ≤ γ.len - ρ)]
    by_cases ha : ρ ≤ u ∧ u + ρ ≤ γ.len
    · -- Case (a): no wrap. The arc is the genuine subinterval `[u-ρ, u+ρ]`.
      obtain ⟨ha1, ha2⟩ := ha
      refine Or.inl ⟨u - ρ, u + ρ, by linarith, by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
      · rintro v ⟨⟨hv0, hvl⟩, hlt⟩
        simp only [dGamma, if_pos hc, min_lt_iff] at hlt
        refine Set.mem_Icc.mpr ?_
        rcases hlt with h | h
        · rw [abs_lt] at h; constructor <;> linarith [h.1, h.2]
        · -- the wrap alternative is impossible here
          have h' : γ.len - ρ < |u - v| := by linarith
          rw [lt_abs] at h'
          rcases h' with h' | h' <;> exfalso <;> linarith
      · exact Or.inr (habs1 _ (by rw [show u - (u - ρ) = ρ by ring, abs_of_pos hρ]))
      · exact Or.inr (habs1 _ (by rw [show u - (u + ρ) = -ρ by ring, abs_neg, abs_of_pos hρ]))
    · -- Case (b) or (c): the arc wraps around the basepoint of the closed curve.
      rcases lt_or_ge u ρ with hlow | hlow
      · -- Case (c), left wrap: `u < ρ`; the arc is `[u+l-ρ, l] ∪ [0, u+ρ]`.
        refine Or.inr ⟨hc, u + γ.len - ρ, u + ρ, by linarith, by linarith, by linarith,
          by linarith, ?_, ?_, ?_⟩
        · rintro v ⟨⟨hv0, hvl⟩, hlt⟩
          simp only [dGamma, if_pos hc, min_lt_iff] at hlt
          rcases hlt with h | h
          · rw [abs_lt] at h
            exact Or.inr (Set.mem_Icc.mpr ⟨hv0, by linarith [h.1]⟩)
          · have h' : γ.len - ρ < |u - v| := by linarith
            rw [lt_abs] at h'
            rcases h' with h' | h'
            · exact absurd h' (not_lt.mpr (by linarith))
            · exact Or.inl (Set.mem_Icc.mpr ⟨by linarith, hvl⟩)
        · exact habs2 _ (by rw [show u - (u + γ.len - ρ) = -(γ.len - ρ) by ring, abs_neg,
            abs_of_pos (by linarith : (0:ℝ) < γ.len - ρ)])
        · exact habs1 _ (by rw [show u - (u + ρ) = -ρ by ring, abs_neg, abs_of_pos hρ])
      · -- Case (b), right wrap: `u ≥ ρ` and `u + ρ > γ.len`; the arc is `[u-ρ, l] ∪ [0, u+ρ-l]`.
        have hb : γ.len < u + ρ := by
          by_contra hcon
          exact ha ⟨hlow, by linarith⟩
        refine Or.inr ⟨hc, u - ρ, u + ρ - γ.len, by linarith, by linarith, by linarith,
          by linarith, ?_, ?_, ?_⟩
        · rintro v ⟨⟨hv0, hvl⟩, hlt⟩
          simp only [dGamma, if_pos hc, min_lt_iff] at hlt
          rcases hlt with h | h
          · rw [abs_lt] at h
            exact Or.inl (Set.mem_Icc.mpr ⟨by linarith [h.2], hvl⟩)
          · have h' : γ.len - ρ < |u - v| := by linarith
            rw [lt_abs] at h'
            rcases h' with h' | h'
            · exact Or.inr (Set.mem_Icc.mpr ⟨hv0, by linarith⟩)
            · exact absurd h' (not_lt.mpr (by linarith))
        · exact habs1 _ (by rw [show u - (u - ρ) = ρ by ring, abs_of_pos hρ])
        · exact habs2 _ (by rw [show u - (u + ρ - γ.len) = γ.len - ρ by ring,
            abs_of_pos (by linarith : (0:ℝ) < γ.len - ρ)])
  · -- `γ` is not closed: `d_γ(u,v) = |u-v|`, and the clamped interval works.
    have hd : ∀ w : ℝ, dGamma γ u w = |u - w| := by
      intro w; simp only [dGamma, if_neg hc]
    refine Or.inl ⟨max 0 (u - ρ), min γ.len (u + ρ), le_max_left _ _, ?_,
      min_le_left _ _, ?_, ?_, ?_, ?_⟩
    · exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith))
    · have h1 : u - ρ ≤ max 0 (u - ρ) := le_max_right _ _
      have h2 : min γ.len (u + ρ) ≤ u + ρ := min_le_right _ _
      linarith
    · rintro v ⟨⟨hv0, hvl⟩, hlt⟩
      simp only [dGamma, if_neg hc, abs_lt] at hlt
      exact Set.mem_Icc.mpr ⟨max_le hv0 (by linarith [hlt.1]),
        le_min hvl (by linarith [hlt.2])⟩
    · rcases le_total (u - ρ) 0 with h | h
      · exact Or.inl (max_eq_left h)
      · refine Or.inr ?_
        rw [max_eq_right h, hd, show u - (u - ρ) = ρ by ring, abs_of_pos hρ]
    · rcases le_total γ.len (u + ρ) with h | h
      · exact Or.inl (min_eq_left h)
      · refine Or.inr ?_
        rw [min_eq_right h, hd, show u - (u + ρ) = -ρ by ring, abs_neg, abs_of_pos hρ]
