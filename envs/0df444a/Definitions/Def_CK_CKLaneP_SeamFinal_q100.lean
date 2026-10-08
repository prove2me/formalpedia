-- Prove2me | Definitions.Def_CK_CKLaneP_SeamFinal_q100
-- name    : CK_CKLaneP_SeamFinal_q100
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T20:51:35.995816+00:00
-- url     : https://prove2.me/theorems/a70b8434-93d2-4bf7-bf02-7f3a9ecd60fb
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamFinal (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamFinal (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamFinal (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamFinal (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamFinal (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneP_SeamFinal_q01


set_option autoImplicit false
namespace CKLaneP
open GeneralCK GeneralCK.Certificates.Mixed Set
/-- The small-scale seam lemma from a checked T-list starting at `κ = 0`. -/
theorem seamT_of_list (hdouble : CanonicalDoubleCapEntropyEndpoints) (qT : ℚ)
    (L : List (ℕ × TCell)) (hL : tlistOK qT 0 L = true) :
    ∀ p q : ℝ, 0 < p → p < q → q ≤ ((qT : ℚ) : ℝ) → SeamAt p q := by
  intro p q hp hpq hqT ys hys0 hysq hysS hstat
  have hq1 : q ≤ 1 := by linarith
  have hk : (((0 : ℚ) : ℚ) : ℝ) ≤ H p / H q := by
    push_cast
    exact div_nonneg (H_nonneg hp.le (by linarith)) (H_nonneg (hp.trans hpq).le hq1)
  exact tlistOK_sound hdouble qT L 0 hL p q hp hpq hqT hk ys hys0 hysq hysS hstat

end CKLaneP


