-- Prove2me | Definitions.Def_CK_CKLaneN1_EdgeSound_part01
-- name    : CK_CKLaneN1_EdgeSound_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:31:51.17422+00:00
-- url     : https://prove2.me/theorems/c4baaecb-0521-4245-8298-a32b955d3c92
-- title:
--   Courtade–Kumar proof module `CKLaneN1.EdgeSound (part 2 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.EdgeSound (part 2 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.EdgeSound (part 2 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.EdgeSound (part 2 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/EdgeSound (part 2 of 5).lean)

import Definitions.Def_CK_CKLaneN1_EdgeSound_part00

set_option autoImplicit false

/-!
# Lane N1: soundness of the leftEdge box checker

`edgeOK_sound`: if `edgeOK B w = true` then for every `(t, z)` in the box with `0 < t < 1`,
`0 < z < 1`, the cutoff-edge value `cPG a (S - a) (H a) (H b)` at `a = m(1-t)`,
`b = m(1 + t(2z-1))` is positive.
-/

namespace CKLaneN1.Edge

open GeneralCK CKLaneE.FP CKLaneN1.Capital Set

/-! ## Elementary helpers -/

theorem Cfun_half_le : Cfun (1 / 2) ≤ ((CHq : ℚ) : ℝ) / 4 := by
  have h3 : ptOk (1 / 3) = true := by decide +kernel
  have h2 : ptOk (1 / 2) = true := by decide +kernel
  have hc : (3 / 2 : ℚ) * (-l1Lo (1 / 3)) + (1 / 2) * lHi (1 / 2) ≤ CHq / 4 := by
    decide +kernel
  have s3 := (ptOk_sound h3).2.2.1
  have s2 := (ptOk_sound h2).2.1
  have hcR : (3 / 2 : ℝ) * (-((l1Lo (1 / 3) : ℚ) : ℝ)) + (1 / 2) * ((lHi (1 / 2) : ℚ) : ℝ) ≤
      ((CHq : ℚ) : ℝ) / 4 := by
    have := rle hc
    push_cast at this ⊢
    linarith
  have e3 : (1 : ℝ) - ((1 / 3 : ℚ) : ℝ) = 2 / 3 := by push_cast; norm_num
  have e2 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by push_cast; norm_num
  rw [e3] at s3
  rw [e2] at s2
  have hl32 : Real.log (3 / 2) = -Real.log (2 / 3) := by
    rw [show (3 / 2 : ℝ) = (2 / 3)⁻¹ by norm_num, Real.log_inv]
  unfold Cfun
  norm_num
  rw [show (3 / 2 : ℝ) * Real.log (3 / 2) = (3 / 2) * Real.log (3 / 2) from rfl, hl32]
  nlinarith

/-- `C ρ ≤ ρ² · CH` for `0 < ρ ≤ 1/2`. -/
theorem Cfun_le_CH {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) :
    Cfun r ≤ r ^ 2 * ((CHq : ℚ) : ℝ) := by
  have hm := Chat_mono hr hr2 (by norm_num)
  have hc := Cfun_half_le
  nlinarith [sq_nonneg r]

/-- `C ρ₁ ≤ ρ₁² · Chi1` from certified logarithms. -/
theorem Cfun_le_Chi {r : ℚ} (hr0 : 0 < r) (hr1 : r < 1) (hp1 : ptOk r = true)
    (hp2 : ptOk (r / (1 + r)) = true) :
    Cfun (r : ℝ) ≤ ((1 + (r : ℝ)) * (-((l1Lo (r / (1 + r)) : ℚ) : ℝ)) +
      (1 - (r : ℝ)) * ((l1Hi r : ℚ) : ℝ)) := by
  have hr0R : (0 : ℝ) < r := by exact_mod_cast hr0
  have hr1R : (r : ℝ) < 1 := by exact_mod_cast hr1
  have s1 := (ptOk_sound hp1).2.2.2
  have s2 := (ptOk_sound hp2).2.2.1
  have e : (1 : ℝ) - ((r / (1 + r) : ℚ) : ℝ) = (1 + (r : ℝ))⁻¹ := by
    push_cast
    field_simp
    ring
  rw [e, Real.log_inv] at s2
  unfold Cfun
  have h1 : (1 + (r : ℝ)) * Real.log (1 + r) ≤ (1 + (r : ℝ)) * (-((l1Lo (r / (1 + r)) : ℚ) : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (1 - (r : ℝ)) * Real.log (1 - r) ≤ (1 - (r : ℝ)) * ((l1Hi r : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left s1 (by linarith)
  linarith

/-! ## Pointwise lower bound -/

/-- The cutoff-edge value dominates the ratio term, the interior cost and the two outer
tangent terms. -/
theorem edge_main_lb {S a b X : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < S - a)
    (hc : S - a < 1 / 2) (hX : (S - 2 * a) / (2 * ((H a + H b) / 2)) ≤ X) :
    e8Theta X / X * ((S - 2 * a) ^ 2 - (b - a) ^ 2) / (4 * ((H a + H b) / 2)) +
        interiorCost a b +
        (2 * entropyInverse ((H a + H b) / 2) - S) *
          e8Theta ((1 - 2 * entropyInverse ((H a + H b) / 2)) / (2 * ((H a + H b) / 2))) +
        ((S - a) - b) * e8Theta ((1 - 2 * (S - a)) / (2 * H b)) ≤
      canonicalPureGap a (S - a) (H a) (H b) := by
  rw [cpg_edge_eq ha hab hbc hc.le]
  have hb2 : b < 1 / 2 := by linarith
  have hHb : 0 < H b := H_pos (by linarith) (by linarith)
  have hHa : 0 < H a := H_pos ha (by linarith)
  have hh0 : 0 < (H a + H b) / 2 := by linarith
  have hh1 : (H a + H b) / 2 < 1 := by
    have := H_lt_one ha.le (by linarith : a < 1 / 2)
    have := H_lt_one (by linarith : (0 : ℝ) ≤ b) hb2
    linarith
  have hq2 : entropyInverse ((H a + H b) / 2) < 1 / 2 := entropyInverse_lt_half hh0.le hh1
  have h1 := F_sub_ge_ratio hh0 (sub_pos.mpr hab) (by linarith : b - a ≤ S - 2 * a) hX
  have h2 := F_tangent (h := (H a + H b) / 2) hh0
    (x0 := 1 - 2 * entropyInverse ((H a + H b) / 2)) (x := 1 - S) (by linarith) (by linarith)
  have h3 := F_tangent (h := H b) hHb (x0 := 1 - 2 * (S - a)) (x := 1 - 2 * b)
    (by linarith) (by linarith)
  have e2 : (1 - S) - (1 - 2 * entropyInverse ((H a + H b) / 2)) =
      2 * entropyInverse ((H a + H b) / 2) - S := by ring
  have e3 : (1 - 2 * b) - (1 - 2 * (S - a)) = 2 * ((S - a) - b) := by ring
  rw [e2] at h2
  rw [e3] at h3
  linarith

/-! ## Term bounds -/

theorem T1_bound {y d h h1 X κ : ℝ} (hd : 0 ≤ d) (hdy : d ≤ y) (hh : 0 < h) (hh1 : h ≤ h1)
    (hX : 0 < X) (hκ : κ ≤ e8Theta X) (hκ0 : 0 ≤ κ) :
    κ / X / (4 * h1) * (y ^ 2 - d ^ 2) ≤ e8Theta X / X * (y ^ 2 - d ^ 2) / (4 * h) := by
  have hyd : 0 ≤ y ^ 2 - d ^ 2 := by nlinarith
  have hk1 : κ / X ≤ e8Theta X / X := div_le_div_of_nonneg_right hκ hX.le
  have hk0 : 0 ≤ κ / X := div_nonneg hκ0 hX.le
  have hh1' : 0 < 4 * h1 := by linarith
  have e1 : κ / X / (4 * h1) ≤ κ / X / (4 * h) :=
    div_le_div_of_nonneg_left hk0 (by linarith) (by linarith)
  have e2 : κ / X / (4 * h) ≤ e8Theta X / X / (4 * h) :=
    div_le_div_of_nonneg_right hk1 (by linarith)
  have e3 : e8Theta X / X * (y ^ 2 - d ^ 2) / (4 * h) = e8Theta X / X / (4 * h) * (y ^ 2 - d ^ 2) := by
    ring
  rw [e3]
  exact mul_le_mul_of_nonneg_right (e1.trans e2) hyd


end CKLaneN1.Edge


