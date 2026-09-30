-- Prove2me | Definitions.Def_CK_CKLaneP_SeamArith
-- name    : CK_CKLaneP_SeamArith
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:54:41.125213+00:00
-- url     : https://prove2.me/theorems/afbbf93c-22dd-4de4-a3a7-7bb88ea6ad97
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamArith` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamArith` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamArith` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamArith (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamArith.lean)

import Definitions.Def_CK_CKLaneP_SeamQBase

-- ===== source module CKLaneP.SeamArith =====
section
/-
Lane P — small arithmetic lemmas for the seam cell checkers (kept out of the big soundness
proofs so that no `nlinarith` runs in a large context).
-/

set_option autoImplicit false

namespace CKLaneP

theorem xmin_le_of {A fH f Z : ℝ} (hf : 0 < f) (hfH : f ≤ fH) (hA : 0 ≤ A) (hAZ : A ≤ Z) :
    A / (2 * fH) ≤ Z / (2 * f) := by
  have h1 : A / (2 * fH) ≤ A / (2 * f) :=
    div_le_div_of_nonneg_left hA (by linarith) (by linarith)
  have h2 : A / (2 * f) ≤ Z / (2 * f) := div_le_div_of_nonneg_right hAZ (by linarith)
  linarith

theorem vmin_le_of {B EH E Z : ℝ} (hB : 0 ≤ B) (hE : 0 < E) (hEH : E ≤ EH) (hBZ : B ≤ Z) :
    B / EH ≤ Z / E := by
  have h1 : B / EH ≤ B / E := div_le_div_of_nonneg_left hB hE hEH
  have h2 : B / E ≤ Z / E := div_le_div_of_nonneg_right hBZ hE.le
  linarith

theorem w_le_wmax_of {t e eL : ℝ} (ht : 0 ≤ t) (heL : 0 < eL) (he : eL ≤ e) :
    (1 - 2 * t) / (2 * e) ≤ 1 / (2 * eL) := by
  have h1 : (1 - 2 * t) / (2 * e) ≤ 1 / (2 * e) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have h2 : 1 / (2 * e) ≤ 1 / (2 * eL) := div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  linarith

theorem bulk_term_of {Jq β d f fH jd : ℝ} (hJq : 0 ≤ Jq) (hβ : 0 ≤ β) (hd : Jq * β ≤ d)
    (hf : 0 < f) (hfH : f ≤ fH) (hjd : 9 / 10 * d ^ 2 / (4 * f ^ 2) ≤ jd) :
    9 / 40 * Jq ^ 2 / fH ^ 2 * β ^ 2 ≤ jd := by
  have hd0 : 0 ≤ Jq * β := mul_nonneg hJq hβ
  have h1 : (Jq * β) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hd0 hd 2
  have hf2 : f ^ 2 ≤ fH ^ 2 := pow_le_pow_left₀ hf.le hfH 2
  have hf20 : 0 < f ^ 2 := by positivity
  have h2 : 9 / 40 * Jq ^ 2 / fH ^ 2 * β ^ 2 = 9 / 40 * (Jq * β) ^ 2 / fH ^ 2 := by ring
  have h3 : 9 / 40 * (Jq * β) ^ 2 / fH ^ 2 ≤ 9 / 40 * (Jq * β) ^ 2 / f ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) hf20 hf2
  have h4 : 9 / 40 * (Jq * β) ^ 2 / f ^ 2 ≤ 9 / 40 * d ^ 2 / f ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) hf20.le
  have h5 : 9 / 40 * d ^ 2 / f ^ 2 = 9 / 10 * d ^ 2 / (4 * f ^ 2) := by
    field_simp
    ring
  linarith

theorem a0_bound_of {e f eL EH Jp β : ℝ} (he : 0 < e) (hef : e ≤ f) (heL : 0 < eL) (heLe : eL ≤ e)
    (hEH : e + f ≤ EH) (hfe : f - e ≤ Jp * β) (hJp : 0 ≤ Jp) (hβ : 0 ≤ β) :
    (f ^ 2 - e ^ 2) / (2 * e * f) ≤ β * (Jp * EH / (2 * eL * eL)) := by
  have hf : 0 < f := lt_of_lt_of_le he hef
  have e1 : (f ^ 2 - e ^ 2) / (2 * e * f) = (f - e) * (e + f) / (2 * e * f) := by ring
  rw [e1]
  have h1 : (f - e) * (e + f) ≤ (Jp * β) * EH :=
    mul_le_mul hfe hEH (by linarith) (le_trans (sub_nonneg.2 hef) hfe)
  have h2 : 2 * eL * eL ≤ 2 * e * f := by nlinarith
  have h0 : 0 < 2 * eL * eL := by positivity
  have h3 : (f - e) * (e + f) / (2 * e * f) ≤ (Jp * β) * EH / (2 * e * f) :=
    div_le_div_of_nonneg_right h1 (by positivity)
  have h4 : (Jp * β) * EH / (2 * e * f) ≤ (Jp * β) * EH / (2 * eL * eL) :=
    div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hJp hβ) (by linarith)) h0 h2
  have h5 : (Jp * β) * EH / (2 * eL * eL) = β * (Jp * EH / (2 * eL * eL)) := by ring
  linarith

theorem ystar_mono_of {A E EH th lam : ℝ} (hA : 0 ≤ A) (hE : 0 < E) (hEH : E ≤ EH) (hlam : 0 ≤ lam)
    (hd : 0 < th - lam * EH) :
    A * E / (th - lam * E) ≤ A * EH / (th - lam * EH) := by
  have hd2 : th - lam * EH ≤ th - lam * E := by nlinarith
  have hd2' : 0 < th - lam * E := lt_of_lt_of_le hd hd2
  have h1 : A * E / (th - lam * E) ≤ A * EH / (th - lam * E) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hEH hA) hd2'.le
  have h2 : A * EH / (th - lam * E) ≤ A * EH / (th - lam * EH) :=
    div_le_div_of_nonneg_left (mul_nonneg hA (by linarith)) hd hd2
  linarith

theorem dip_mono_of {M Y E EL : ℝ} (hM : 0 ≤ M) (hEL : 0 < EL) (hE : EL ≤ E) :
    M * Y ^ 2 / (2 * E) ≤ M * Y ^ 2 / (2 * EL) :=
  div_le_div_of_nonneg_left (mul_nonneg hM (sq_nonneg _)) (by linarith) (by linarith)

end CKLaneP

end


