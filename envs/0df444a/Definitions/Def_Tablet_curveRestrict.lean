-- Prove2me | Definitions.Def_Tablet_curveRestrict
-- name    : Tablet_curveRestrict
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:47:47.802178+00:00
-- url     : https://prove2.me/theorems/0264552f-d103-59d0-95b5-74bf0c039642
-- title:
--   curve Restrict
-- statement:
--   Definitions and structural lemmas for curve Restrict, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/curveRestrict.lean

import Definitions.Def_Tablet_Curve
set_option autoImplicit false
open Set
noncomputable def curveRestrict {E : Type*} [MetricSpace E] (γ : Curve E) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.len) : Curve E where
-- BODY
  len := b - a
  len_nonneg := by linarith
  toFun := fun u => γ.toFun (a + min (b - a) (max 0 u))
  clamped := by
    intro u
    set v : ℝ := min (b - a) (max 0 u) with hv_def
    have hv0 : (0:ℝ) ≤ v := le_min (by linarith) (le_max_left _ _)
    have hv1 : v ≤ b - a := min_le_left _ _
    have step1 : max (0:ℝ) v = v := le_antisymm (max_le hv0 le_rfl) (le_max_right _ _)
    have step2 : min (b - a) v = v := le_antisymm (min_le_right _ _) (le_min hv1 le_rfl)
    show γ.toFun (a + v) = γ.toFun (a + min (b - a) (max 0 v))
    rw [step1, step2]
  unitSpeed := by
    have hEq : Set.EqOn (fun u => γ.toFun (a + min (b - a) (max 0 u)))
        (fun u => γ.toFun (a + u)) (Set.Icc 0 (b - a)) := by
      intro u hu
      obtain ⟨hu0, hu1⟩ := hu
      simp only []
      rw [max_eq_right hu0, min_eq_right hu1]
    intro x hx y hy
    rw [eVariationOn.eq_of_eqOn (hEq.mono Set.inter_subset_left)]
    have hmono : MonotoneOn (fun u : ℝ => a + u) (Set.Icc 0 (b - a)) := by
      intro p _ q _ hpq; simpa using hpq
    have key := eVariationOn.comp_inter_Icc_eq_of_monotoneOn γ.toFun (fun u : ℝ => a + u) hmono hx hy
    have himg : (fun u : ℝ => a + u) '' Set.Icc 0 (b - a) = Set.Icc a b := by
      ext z
      constructor
      · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩; constructor <;> simp <;> linarith
      · rintro ⟨hz0, hz1⟩; exact ⟨z - a, ⟨by linarith, by linarith⟩, by ring⟩
    have hfun : (fun u => γ.toFun (a + u)) = γ.toFun ∘ (fun u : ℝ => a + u) := rfl
    rw [hfun, key, himg]
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    rcases le_total x y with hxy | hyx
    · have hset : Set.Icc a b ∩ Set.Icc (a + x) (a + y)
          = Set.Icc 0 γ.len ∩ Set.Icc (a + x) (a + y) := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩
      rw [hset]
      have := γ.unitSpeed (x := a + x) ⟨by linarith, by linarith⟩
        (y := a + y) ⟨by linarith, by linarith⟩
      rw [this]
      congr 1
      push_cast
      ring
    · rw [eVariationOn.subsingleton, ENNReal.ofReal_of_nonpos (by push_cast; nlinarith)]
      exact (Set.subsingleton_Icc_of_ge (by linarith)).anti Set.inter_subset_right


