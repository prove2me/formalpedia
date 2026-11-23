-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerMore
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerMore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:18.937699+00:00
-- url     : https://prove2.me/theorems/f8435e09-a799-403e-868b-b62751b4a6c3
-- title:
--   Imports Ter More
-- statement:
--   Definitions and structural lemmas for Imports Ter More, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsTerMore.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.InductiveNormBound
theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w^2 - 1‖ := by
  have e : w^2 - 1 = (w - 1) * ((w - 1) + 2) := by ring
  rw [e, norm_mul]
  have h2 : (3/2 : ℝ) ≤ ‖(w - 1) + 2‖ := by
    have h3 := norm_sub_le ((w - 1) + 2) (w - 1)
    have h4 : (w - 1) + 2 - (w - 1) = (2:ℂ) := by ring
    rw [h4] at h3
    have : ‖(2:ℂ)‖ = 2 := by simp
    linarith
  have h0 := norm_nonneg (w - 1)
  nlinarith
theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  have key : ∀ k : ℕ, (3/2 : ℝ)^k * ‖z - 1‖ ≤ ‖z^(2^k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := step (z^(2^k)) (hz _)
      have e : (z^(2^k))^2 = z^(2^(k+1)) := by rw [← pow_mul, ← pow_succ]
      rw [e] at hs
      have hp : (3/2:ℝ)^(k+1) = (3/2)^k * (3/2) := pow_succ _ _
      rw [hp]
      nlinarith [ih, hs]
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ‖z - 1‖) (by norm_num : (1:ℝ) < 3/2)
  have h1 := key k
  have h2 := hz (2^k)
  have h3 : 1 < (3/2:ℝ)^k * ‖z - 1‖ := by
    rw [div_lt_iff₀ hpos] at hk; linarith
  linarith
example : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := main
end GlobalTheory.InductiveNormBound


