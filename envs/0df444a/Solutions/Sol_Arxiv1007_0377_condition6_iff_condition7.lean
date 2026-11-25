-- Prove2me | solution 1 for Arxiv1007_0377.condition6_iff_condition7
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:40:57.604317+00:00
-- url     : https://prove2.me/submissions/1843ee3a-1118-402b-8e19-6a4697feb4c9

import Mathlib
import Definitions.Def_Arxiv1007_0377_Basic

open Complex Polynomial

namespace Arxiv1007_0377

theorem condition6_iff_condition7 (ε μ : ℂ) (hμ : μ.im ≠ 0) :
    (Condition6 ε μ → Condition7 ε μ) ∧
    (Condition6 ε μ ↔ Condition7 ε μ ∧ epsMuRe ε μ ≤ 0) := by
  set s := ‖ε‖ * ‖μ‖ with hs
  have s0 : 0 ≤ s := by positivity
  have hs2 : s ^ 2 = (ε.re * μ.re - ε.im * μ.im) ^ 2 + (ε.re * μ.im + ε.im * μ.re) ^ 2 := by
    rw [hs, mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    ring
  have h6 : Condition6 ε μ ↔ ε.re * μ.re - ε.im * μ.im + s = 0 := by
    unfold Condition6 branchRadicand; rfl
  have h7 : Condition7 ε μ ↔ ε.re * μ.im + ε.im * μ.re = 0 := by
    unfold Condition7
    constructor
    · intro h; rw [h]; field_simp; ring
    · intro h; field_simp; linarith
  have hre : epsMuRe ε μ = ε.re * μ.re - ε.im * μ.im := rfl
  rw [h6, h7, hre]
  set a := ε.re * μ.re - ε.im * μ.im
  set b := ε.re * μ.im + ε.im * μ.re
  have fwd : a + s = 0 → b = 0 ∧ a ≤ 0 := by
    intro h
    have hsa : s = -a := by linarith
    have : b ^ 2 = 0 := by rw [hsa] at hs2; nlinarith
    exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this, by linarith⟩
  refine ⟨fun h => (fwd h).1, fwd, ?_⟩
  rintro ⟨hb, ha⟩
  rw [hb] at hs2
  have : (s - (-a)) * (s + (-a)) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · nlinarith

end Arxiv1007_0377
open Arxiv1007_0377 in
theorem solution (ε μ : ℂ) (hμ : μ.im ≠ 0) :
    (Condition6 ε μ → Condition7 ε μ) ∧
    (Condition6 ε μ ↔ Condition7 ε μ ∧ epsMuRe ε μ ≤ 0) := condition6_iff_condition7 ε μ hμ
