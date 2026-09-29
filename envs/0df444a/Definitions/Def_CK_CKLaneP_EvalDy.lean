-- Prove2me | Definitions.Def_CK_CKLaneP_EvalDy
-- name    : CK_CKLaneP_EvalDy
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T08:56:49.427268+00:00
-- url     : https://prove2.me/theorems/382fbfb1-858c-465f-8d56-987d7ed9b6a9
-- title:
--   Courtade–Kumar proof module `CKLaneP.EvalDy` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.EvalDy` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.EvalDy` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.EvalDy (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/EvalDy.lean)

import Definitions.Def_CK_CKLaneP_EvalTheta
import Definitions.Def_CK_CKLaneP_FastLog

-- ===== source module CKLaneP.EvalDy =====
section
/-
Lane P — contact-point data `VD` from dyadic inputs via the fixed-point logarithm `lnDy`.

`VD.ofDy P Q n l2 N` has `v = N / 2^P` and log data from `lnDy` (scale `2^Q`).
Soundness `VD.ofDy_sound` needs `1 ≤ N`, `2N ≤ 2^P` and a sound `l2` (e.g. `l2c64`, Q = 64).
-/

set_option autoImplicit false

namespace CKLaneP

/-- Literal fixed-point bounds of `2^64 log 2`. -/
def l2c : ℕ × ℕ := (12786308645202655659, 12786308645202655660)

theorem l2c_sound : ((l2c.1 : ℕ) : ℝ) ≤ 2 ^ 64 * Real.log 2 ∧
    2 ^ 64 * Real.log 2 ≤ ((l2c.2 : ℕ) : ℝ) := by
  have h := log2D_bounds
  unfold L2loD L2hiD at h
  push_cast at h
  simp only [l2c]
  push_cast
  have hp : (0 : ℝ) ≤ 2 ^ 64 := by positivity
  have e1 := mul_le_mul_of_nonneg_left h.1 hp
  have e2 := mul_le_mul_of_nonneg_left h.2 hp
  constructor
  · have : (2 : ℝ) ^ 64 * ((12786308645202655659 : ℝ) / 18446744073709551616) =
        12786308645202655659 := by norm_num
    linarith
  · have : (2 : ℝ) ^ 64 * ((12786308645202655660 : ℝ) / 18446744073709551616) =
        12786308645202655660 := by norm_num
    linarith

namespace VD

/-- Contact data at `v = N / 2^P` from fixed-point logs. -/
def ofDy (P Q n : ℕ) (l2 : ℕ × ℕ) (N : ℕ) : VD :=
  let r1 := lnDy P Q n l2 N
  let r2 := lnDy P Q n l2 (2 ^ P - N)
  ⟨(N : ℚ) / ((2 ^ P : ℕ) : ℚ), -((r1.2 : ℚ) / ((2 ^ Q : ℕ) : ℚ)), -((r1.1 : ℚ) / ((2 ^ Q : ℕ) : ℚ)),
    -((r2.2 : ℚ) / ((2 ^ Q : ℕ) : ℚ)), -((r2.1 : ℚ) / ((2 ^ Q : ℕ) : ℚ))⟩

/-- Decidable precondition. -/
def okDy (P : ℕ) (N : ℕ) : Bool := decide (1 ≤ N ∧ 2 * N ≤ 2 ^ P)

theorem ofDy_sound {P Q n : ℕ} {l2 : ℕ × ℕ} {N : ℕ}
    (hl2 : (l2.1 : ℝ) ≤ 2 ^ Q * Real.log 2 ∧ 2 ^ Q * Real.log 2 ≤ (l2.2 : ℝ))
    (h : okDy P N = true) : (ofDy P Q n l2 N).Sound := by
  unfold okDy at h
  obtain ⟨h1, h2⟩ := of_decide_eq_true h
  have hP : 0 < 2 ^ P := Nat.two_pow_pos P
  have hN2 : 1 ≤ 2 ^ P - N := by omega
  obtain ⟨a1, a2⟩ := lnDy_sound (P := P) (Q := Q) (n := n) hl2 h1
  obtain ⟨b1, b2⟩ := lnDy_sound (P := P) (Q := Q) (n := n) hl2 hN2
  have hQ : (0 : ℝ) < 2 ^ Q := by positivity
  have hPR : (0 : ℝ) < 2 ^ P := by positivity
  have hvR : ((((N : ℚ) / ((2 ^ P : ℕ) : ℚ) : ℚ)) : ℝ) = (N : ℝ) / 2 ^ P := by push_cast; ring
  have h1v : 1 - (N : ℝ) / 2 ^ P = ((2 ^ P - N : ℕ) : ℝ) / 2 ^ P := by
    rw [Nat.cast_sub (by omega : N ≤ 2 ^ P)]; push_cast; field_simp
  unfold ofDy Sound
  simp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (0 : ℚ) < (N : ℚ) := by exact_mod_cast h1
    positivity
  · rw [div_le_iff₀ (by positivity)]
    have : ((2 * N : ℕ) : ℚ) ≤ ((2 ^ P : ℕ) : ℚ) := by exact_mod_cast h2
    push_cast at this ⊢
    linarith
  all_goals
    first
      | (rw [hvR, h1v]; push_cast
         first
           | (rw [div_le_iff₀ hQ]; linarith)
           | (rw [le_div_iff₀ hQ]; linarith)
           | (rw [le_neg, neg_neg, div_le_iff₀ hQ]; linarith)
           | (rw [le_neg, neg_neg, le_div_iff₀ hQ]; linarith)
           | (rw [neg_le, neg_neg, le_div_iff₀ hQ]; linarith)
           | (rw [neg_le, neg_neg, div_le_iff₀ hQ]; linarith))
      | (rw [hvR]; push_cast
         first
           | (rw [div_le_iff₀ hQ]; linarith)
           | (rw [le_div_iff₀ hQ]; linarith)
           | (rw [le_neg, neg_neg, div_le_iff₀ hQ]; linarith)
           | (rw [le_neg, neg_neg, le_div_iff₀ hQ]; linarith)
           | (rw [neg_le, neg_neg, le_div_iff₀ hQ]; linarith)
           | (rw [neg_le, neg_neg, div_le_iff₀ hQ]; linarith))

end VD

/-! ### Benchmark and pilot -/

/-- Pilot: `v = 1/10 ≈ 1717986918 / 2^34`; Θ lower bound 4.9 at `x = 2`. -/
def pilotVD2 : VD := VD.ofDy 34 64 20 l2c 1717986918

theorem pilotVD2_numbers : VD.okDy 34 1717986918 = true ∧
    1 - 2 * pilotVD2.v ≤ 2 * 2 * pilotVD2.Hlo ∧ 0 < pilotVD2.a1 + pilotVD2.a2 ∧
      (49 / 10 : ℚ) ≤ pilotVD2.Slo ∧ pilotVD2.Shi ≤ 491 / 100 ∧ pilotVD2.v < 1 / 2 := by
  decide +kernel

theorem pilot2_theta_two : (49 / 10 : ℝ) ≤ GeneralCK.e8Theta 2 := by
  have hn := pilotVD2_numbers
  have hd : pilotVD2.Sound := VD.ofDy_sound l2c_sound hn.1
  have h := theta_ge_Slo hd hn.2.2.2.2.2 (xq := 2) (x := 2) (by norm_num) (by norm_num) hn.2.1
  have h2 : ((49 / 10 : ℚ) : ℝ) ≤ ((pilotVD2.Slo : ℚ) : ℝ) := by exact_mod_cast hn.2.2.2.1
  have e : ((49 / 10 : ℚ) : ℝ) = 49 / 10 := by norm_num
  linarith

end CKLaneP

end


