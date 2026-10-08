-- Prove2me | Definitions.Def_CK_CKLaneP_SeamFinal_q01
-- name    : CK_CKLaneP_SeamFinal_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T20:00:01.026186+00:00
-- url     : https://prove2.me/theorems/623f8f0f-dcc6-4071-b9c1-5ddcacaf0580
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamFinal (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamFinal (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamFinal (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamFinal (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamFinal (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneP_SeamFinal_q00

set_option autoImplicit false
namespace CKLaneP
open GeneralCK GeneralCK.Certificates.Mixed Set
theorem tlistOK_sound (hdouble : CanonicalDoubleCapEntropyEndpoints) (qT : ℚ) :
    ∀ (L : List (ℕ × TCell)) (k : ℚ), tlistOK qT k L = true →
    ∀ p q : ℝ, 0 < p → p < q → q ≤ ((qT : ℚ) : ℝ) → ((k : ℚ) : ℝ) ≤ H p / H q → SeamAt p q := by
  intro L
  induction L with
  | nil =>
      intro k h p q hp hpq _ hk ys _ hysq hysS _
      have hk1 : (1 : ℚ) ≤ k := of_decide_eq_true h
      have hk1R : (1 : ℝ) ≤ ((k : ℚ) : ℝ) := by exact_mod_cast hk1
      exfalso
      have hq12 : q ≤ 1 / 2 := by linarith
      have hHpq : H p < H q := H_strictMonoOn ⟨hp.le, by linarith⟩ ⟨(hp.trans hpq).le, hq12⟩ hpq
      have hHp : 0 < H p := H_pos hp (by linarith)
      have hHq : 0 < H q := hHp.trans hHpq
      have : H p / H q < 1 := by rw [div_lt_one hHq]; exact hHpq
      linarith
  | cons hd rest ih =>
      obtain ⟨kind, c⟩ := hd
      intro k h p q hp hpq hqT hk
      simp only [tlistOK, Bool.and_eq_true] at h
      obtain ⟨⟨hkc, htc⟩, hrest⟩ := h
      obtain ⟨hcq, hck⟩ := of_decide_eq_true hkc
      rcases le_total (H p / H q) ((c.k1 : ℚ) : ℝ) with h1 | h1
      · intro ys hys0 _ hysS hstat
        have hqT' : q ≤ ((c.qT : ℚ) : ℝ) := by rw [hcq]; exact hqT
        have hk' : ((c.k0 : ℚ) : ℝ) ≤ H p / H q := by rw [hck]; exact hk
        exact tcheck_sound hdouble kind c htc hp hpq hqT' hk' h1 hys0 hysS hstat
      · exact ih c.k1 hrest p q hp hpq hqT h1

end CKLaneP


