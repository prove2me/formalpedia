-- Prove2me | solution 1 for AlonMilman.PropertyT.regularRep_zero_sum_moved
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:24:53.858581+00:00
-- url     : https://prove2.me/submissions/b77b863f-7cf2-4194-b939-39eeb42789e1

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_regularRep

open Matrix
open AlonMilman.PropertyT

/-- The regular representation acts by translation: `(π(t) v) w = v (t⁻¹ w)`. -/
private theorem regularRep_apply {T : Type} [Group T] [Fintype T] [DecidableEq T]
    (t : T) (v : T → ℂ) (w : T) : (regularRep ℂ t *ᵥ v) w = v (t⁻¹ * w) := by
  classical
  have hsum : ∀ u : T, regularRep ℂ t w u * v u
      = if u = t⁻¹ * w then v u else 0 := by
    intro u
    by_cases h : u = t⁻¹ * w
    · subst h
      have : w * (t⁻¹ * w)⁻¹ = t := by group
      simp [regularRep, this]
    · have hne : w * u⁻¹ ≠ t := by
        intro hc
        apply h
        have : u = t⁻¹ * w := by
          rw [← hc]; group
        exact this
      simp [regularRep, hne, h]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun u _ => hsum u]
  simp

theorem solution {H T : Type} [Group H] [Group T] [Fintype T] [DecidableEq T]
    (φ : H →* T) (hφ : Function.Surjective φ) (v : T → ℂ) (hv : ∑ t, v t = 0) (hv0 : v ≠ 0) :
    ∃ h : H, regularRep ℂ (φ h) *ᵥ v ≠ v := by
  by_contra hcon
  push_neg at hcon
  -- every group element translates `v` to itself, so `v` is constant
  have hconst : ∀ u w : T, v u = v w := by
    intro u w
    obtain ⟨h, hh⟩ := hφ (w * u⁻¹)
    have h1 : regularRep ℂ (φ h) *ᵥ v = v := hcon h
    have h2 := congrFun h1 w
    rw [regularRep_apply] at h2
    rw [hh] at h2
    have h3 : (w * u⁻¹)⁻¹ * w = u := by group
    rw [h3] at h2
    exact h2
  -- a constant with zero sum is zero
  have hzero : ∀ w : T, v w = 0 := by
    intro w
    have hs : ∑ t : T, v t = (Fintype.card T : ℂ) * v w := by
      rw [Finset.sum_congr rfl fun t _ => hconst t w]
      simp [Finset.sum_const, Finset.card_univ]
    rw [hv] at hs
    have hcard : (Fintype.card T : ℂ) ≠ 0 := by
      have hp : 0 < Fintype.card T := Fintype.card_pos
      exact Nat.cast_ne_zero.mpr (by omega)
    exact (mul_eq_zero.mp hs.symm).resolve_left hcard
  exact hv0 (funext fun w => hzero w)
