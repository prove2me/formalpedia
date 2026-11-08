-- Prove2me | solution 1 for AirlineYieldMgmt.BookingLimits.terminal_value_concave
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:13:37.253386+00:00
-- url     : https://prove2.me/submissions/3fb7ebd4-1a35-4182-846d-a4077bf90735

import Mathlib
import Definitions.Def_AirlineYieldMgmt_BookingLimits_Model
import Theorems.Thm_AirlineYieldMgmt_BookingLimits_lemma1_binomial_convex

namespace AirlineYieldMgmt.BookingLimits

open Finset

theorem binomExp_neg' (x : ℕ) (γ : ℝ) (f : ℝ → ℝ) :
    binomExp x γ (fun y => -f y) = -binomExp x γ f := by
  unfold binomExp
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- Degenerate case `γ = 0`: `Y(x) ≡ 0`. -/
theorem binomExp_zero' (x : ℕ) (f : ℝ → ℝ) : binomExp x 0 f = f 0 := by
  unfold binomExp
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos x)) h

/-- Degenerate case `γ = 1`: `Y(x) ≡ x`. -/
theorem binomExp_one' (x : ℕ) (f : ℝ → ℝ) : binomExp x 1 f = f x := by
  unfold binomExp
  rw [Finset.sum_eq_single x]
  · simp
  · intro k hk hkx
    have : k < x := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkx
    have : x - k ≠ 0 := by omega
    simp [zero_pow this]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self x)) h

/-- Lemma 1 including the boundary cases `γ ∈ {0, 1}`; the interior case is Lemma 1. -/
theorem binomExp_mono_convex' (f : ℝ → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0))
    (hf_convex : ConvexOn ℝ (Set.Ici 0) f) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    Monotone (fun x : ℕ => binomExp x γ f) ∧
      ∀ x : ℕ, binomExp (x + 1) γ f - binomExp x γ f ≤
        binomExp (x + 2) γ f - binomExp (x + 1) γ f := by
  rcases hγ0.lt_or_eq with hγ0' | rfl
  · rcases hγ1.lt_or_eq with hγ1' | rfl
    · exact lemma1_binomial_convex f hf_mono hf_convex γ hγ0' hγ1'
    · simp only [binomExp_one']
      refine ⟨fun a b hab => ?_, fun x => ?_⟩
      · exact hf_mono (by simp [Set.mem_Ici]) (by simp [Set.mem_Ici]) (by exact_mod_cast hab)
      · have hk0 : (x : ℝ) ∈ Set.Ici (0 : ℝ) := by simp [Set.mem_Ici]
        have hk2 : (x : ℝ) + 2 ∈ Set.Ici (0 : ℝ) := by simp [Set.mem_Ici]; positivity
        have := hf_convex.2 hk0 hk2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
          (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
        simp only [smul_eq_mul] at this
        have e : 1 / 2 * (x : ℝ) + 1 / 2 * ((x : ℝ) + 2) = (x : ℝ) + 1 := by ring
        rw [e] at this
        push_cast
        linarith
  · simp only [binomExp_zero']
    exact ⟨fun _ _ _ => le_refl _, fun _ => by simp⟩

end AirlineYieldMgmt.BookingLimits

open AirlineYieldMgmt.BookingLimits in
theorem solution {m : ℕ} (M : Model m)
    (hβ0 : 0 ≤ M.β) (hβ1 : M.β ≤ 1)
    (hπ_convex : ConvexOn ℝ (Set.Ici 0) M.π) (hπ_mono : MonotoneOn M.π (Set.Ici 0)) :
    Antitone (M.U 0) ∧
      ∀ x : ℕ, M.U 0 (x + 2) - M.U 0 (x + 1) ≤ M.U 0 (x + 1) - M.U 0 x := by
  obtain ⟨h1, h2⟩ := binomExp_mono_convex' M.π hπ_mono hπ_convex (1 - M.β) (by linarith)
    (by linarith)
  have hU : ∀ x, M.U 0 x = -binomExp x (1 - M.β) M.π := fun x => binomExp_neg' x _ _
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · rw [hU, hU]; exact neg_le_neg (h1 hab)
  · rw [hU, hU, hU]; linarith [h2 x]
