-- Prove2me | Definitions.Def_Tablet_curveConcat
-- name    : Tablet_curveConcat
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:47:48.33005+00:00
-- url     : https://prove2.me/theorems/89f5954f-873f-444d-8977-8e7cab3d65c5
-- title:
--   curve Concat
-- statement:
--   Definitions and structural lemmas for curve Concat, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/curveConcat.lean

import Definitions.Def_Tablet_Curve
set_option autoImplicit false
open Set
noncomputable def curveConcat {E : Type*} [MetricSpace E] (γ₁ γ₂ : Curve E)
    (h : γ₁.toFun γ₁.len = γ₂.toFun 0) : Curve E where
-- BODY
  len := γ₁.len + γ₂.len
  len_nonneg := by have := γ₁.len_nonneg; have := γ₂.len_nonneg; linarith
  toFun := fun t => if t ≤ γ₁.len then γ₁.toFun t else γ₂.toFun (t - γ₁.len)
  clamped := by
    intro t
    have h1 := γ₁.len_nonneg
    have h2 := γ₂.len_nonneg
    rcases le_or_gt t γ₁.len with ht | ht
    · rcases le_or_gt 0 t with ht0 | ht0
      · rw [if_pos ht, max_eq_right ht0, min_eq_right (by linarith), if_pos ht]
      · rw [if_pos ht, max_eq_left (le_of_lt ht0),
          min_eq_right (by linarith : (0:ℝ) ≤ γ₁.len + γ₂.len), if_pos h1]
        rw [γ₁.clamped t, max_eq_left (le_of_lt ht0), min_eq_right h1]
    · rw [if_neg (not_le.mpr ht)]
      rcases le_or_gt t (γ₁.len + γ₂.len) with hb | hb
      · rw [max_eq_right (by linarith), min_eq_right hb, if_neg (not_le.mpr ht)]
      · rw [max_eq_right (by linarith), min_eq_left (le_of_lt hb)]
        rcases eq_or_lt_of_le h2 with h2e | h2p
        · rw [if_pos (by linarith), ← h2e]
          rw [γ₂.clamped (t - γ₁.len), ← h2e,
            max_eq_right (by linarith : (0:ℝ) ≤ t - γ₁.len),
            min_eq_left (by linarith : (0:ℝ) ≤ t - γ₁.len)]
          rw [add_zero, h]
        · rw [if_neg (by simp only [not_le]; linarith)]
          rw [γ₂.clamped (t - γ₁.len)]
          have : min γ₂.len (max 0 (t - γ₁.len)) = γ₂.len := by
            rw [max_eq_right (by linarith)]; exact min_eq_left (by linarith)
          rw [this]
          congr 1
          ring
  unitSpeed := by
    have h1 := γ₁.len_nonneg
    have h2 := γ₂.len_nonneg
    set F : ℝ → E := fun t => if t ≤ γ₁.len then γ₁.toFun t else γ₂.toFun (t - γ₁.len) with hF
    have part1 : HasUnitSpeedOn F (Set.Icc 0 γ₁.len) := by
      have hEq : Set.EqOn F γ₁.toFun (Set.Icc 0 γ₁.len) := by
        intro u hu; simp only [hF]; rw [if_pos hu.2]
      intro x hx y hy
      rw [eVariationOn.eq_of_eqOn (hEq.mono Set.inter_subset_left)]
      exact γ₁.unitSpeed hx hy
    have part2 : HasUnitSpeedOn F (Set.Icc γ₁.len (γ₁.len + γ₂.len)) := by
      have hEq : Set.EqOn F (fun u => γ₂.toFun (u - γ₁.len))
          (Set.Icc γ₁.len (γ₁.len + γ₂.len)) := by
        intro u hu
        simp only [hF]
        rcases le_or_gt u γ₁.len with hu1 | hu1
        · rw [if_pos hu1]
          have : u = γ₁.len := le_antisymm hu1 hu.1
          subst this
          simp [h]
        · rw [if_neg (not_le.mpr hu1)]
      intro x hx y hy
      rw [eVariationOn.eq_of_eqOn (hEq.mono Set.inter_subset_left)]
      have hmono : MonotoneOn (fun u : ℝ => u - γ₁.len) (Set.Icc γ₁.len (γ₁.len + γ₂.len)) := by
        intro p _ q _ hpq; simpa using hpq
      have key := eVariationOn.comp_inter_Icc_eq_of_monotoneOn γ₂.toFun
        (fun u : ℝ => u - γ₁.len) hmono hx hy
      have himg : (fun u : ℝ => u - γ₁.len) '' Set.Icc γ₁.len (γ₁.len + γ₂.len)
          = Set.Icc 0 γ₂.len := by
        ext z
        constructor
        · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩; constructor <;> simp <;> linarith
        · rintro ⟨hz0, hz1⟩; exact ⟨z + γ₁.len, ⟨by linarith, by linarith⟩, by ring⟩
      have hfun : (fun u => γ₂.toFun (u - γ₁.len)) = γ₂.toFun ∘ (fun u : ℝ => u - γ₁.len) := rfl
      rw [hfun, key, himg]
      obtain ⟨hx0, hx1⟩ := hx
      obtain ⟨hy0, hy1⟩ := hy
      have := γ₂.unitSpeed (x := x - γ₁.len) ⟨by linarith, by linarith⟩
        (y := y - γ₁.len) ⟨by linarith, by linarith⟩
      rw [this]
      congr 1
      push_cast
      ring
    exact HasUnitSpeedOn.Icc_Icc part1 part2


