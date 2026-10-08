-- Prove2me | Definitions.Def_CK_CKLaneN4_LU_OwnerBridge
-- name    : CK_CKLaneN4_LU_OwnerBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T07:02:57.622154+00:00
-- url     : https://prove2.me/theorems/3a980f27-1199-47dc-8744-378f15b95973
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LU.OwnerBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LU.OwnerBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LU.OwnerBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LU.OwnerBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LU/OwnerBridge.lean)

import Definitions.Def_CK_CKLaneN4_LU_Tree
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperWideHalfCollar

-- ===== source module CKLaneN4.LU.OwnerBridge =====
section
/-
Lane N4b — from the certified chart box to the corpus owner proposition.

`cpg_eq_gexpr`: on `0 < a < b < 1/2`, `canonicalPureGap a (1/2) (H a) (H b) = Gexpr a b`
(corpus `canonicalPureGap_leftUpper_radial_eq` + `eta (H b) = (1 - 2b) J b`).
`owner_of_box`: a certified root box `[0, A] × [0, 1]` with `A/2^64 ≥ 5/11` yields
`GeneralCK.LeftUpperOutsideWideHalfCollarAndNarrowOwner`.
-/

set_option autoImplicit false

namespace CKLaneN4.LU

open GeneralCK

theorem eta_H_eq_kfun {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 1 / 2) : eta (H b) = kfun b := by
  rw [eta_eq_profile (H_nonneg hb.le (by linarith)) (H_le_one b), entropyInverse_H_lower hb.le hb2]
  rfl

theorem cpg_eq_gexpr {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1 / 2) :
    canonicalPureGap a (1 / 2) (H a) (H b) = Gexpr a b := by
  rw [canonicalPureGap_leftUpper_radial_eq ha hab hb, eta_H_eq_kfun (ha.trans hab) hb.le]
  unfold Gexpr Cfun Vfun hAvg
  ring

theorem owner_of_box {A : ℕ} (hA : (5 : ℝ) / 11 ≤ (A : ℝ) / 2 ^ 64)
    (hroot : BoxGood 0 A 0 18446744073709551616) :
    LeftUpperOutsideWideHalfCollarAndNarrowOwner := by
  intro a b ha hab hb ha511 _
  rw [cpg_eq_gexpr ha hab hb]
  have h12 : 0 < 1 / 2 - a := by linarith
  have ht : 0 < (b - a) / (1 / 2 - a) := div_pos (by linarith) h12
  have ht1 : (b - a) / (1 / 2 - a) ≤ 1 := by rw [div_le_one h12]; linarith
  have hbt : bAt a ((b - a) / (1 / 2 - a)) = b := by
    unfold bAt; rw [div_mul_cancel₀ _ h12.ne']; ring
  rw [← hbt]
  have e0 : ((0 : ℕ) : ℝ) / 2 ^ 64 = 0 := by simp
  have e1 : ((18446744073709551616 : ℕ) : ℝ) / 2 ^ 64 = 1 := by norm_num
  refine hroot a _ ?_ ?_ ?_ ?_ ha ht
  · rw [e0]; exact ha.le
  · linarith
  · rw [e0]; exact ht.le
  · rw [e1]; exact ht1

end CKLaneN4.LU

end


