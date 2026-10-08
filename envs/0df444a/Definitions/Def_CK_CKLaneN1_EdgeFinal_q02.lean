-- Prove2me | Definitions.Def_CK_CKLaneN1_EdgeFinal_q02
-- name    : CK_CKLaneN1_EdgeFinal_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T17:38:06.658034+00:00
-- url     : https://prove2.me/theorems/eb46d783-dfee-4fcc-a2b2-055fb9282d12
-- title:
--   Courtade–Kumar proof module `CKLaneN1.EdgeFinal (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.EdgeFinal (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.EdgeFinal (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.EdgeFinal (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/EdgeFinal (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneN1_EdgeFinal_q01

set_option autoImplicit false
namespace CKLaneN1.Edge
open GeneralCK SmallMeanPhiCutoff
/-- Positivity of the cutoff-edge value in the `(t, z)` chart. -/
theorem edge_pos_tz {t z : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    0 < canonicalPureGap (1 / 20000 * (1 - t)) (1 / 10000 - 1 / 20000 * (1 - t))
      (H (1 / 20000 * (1 - t))) (H (1 / 20000 * (1 + t * (2 * z - 1)))) := by
  have hroot : edgeRoot.Mem t z 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [edgeRoot] <;> push_cast <;> linarith
  obtain ⟨q, hq, hmem⟩ := PT.cover edgeRoot edgeTree hroot
  have hok := PT.allLeaves_sound edgeTree_ok q hq
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hmem
  unfold edgeLeafOK at hok
  split_ifs at hok with hc
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hT, -⟩, -⟩, hZ⟩ := hok
    have hTR : (1023 / 1024 : ℝ) ≤ t := by
      have := rle hT
      simp only [TCq] at this
      push_cast at this
      linarith
    have hZR : z ≤ 1 / 2048 := by
      have := rle hZ
      simp only [ZCq] at this
      push_cast at this
      linarith
    exact corner_pos hTR ht1 hz0 hZR
  · exact edgeOK_sound hok h1 h2 h3 h4 ht0 ht1 hz0 hz1

end CKLaneN1.Edge


