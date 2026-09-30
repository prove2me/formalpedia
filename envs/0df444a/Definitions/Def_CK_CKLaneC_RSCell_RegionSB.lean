-- Prove2me | Definitions.Def_CK_CKLaneC_RSCell_RegionSB
-- name    : CK_CKLaneC_RSCell_RegionSB
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:47:29.744714+00:00
-- url     : https://prove2.me/theorems/f5d936bc-bfec-4e15-b83f-a43fcd94985f
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSCell.RegionSB` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSCell.RegionSB` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSCell.RegionSB` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSCell.RegionSB (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSCell/RegionSB.lean)

import Definitions.Def_CK_CKLaneC_RSCell_Region

-- ===== source module CKLaneC.RSCell.RegionSB =====
section

/-!
# Lane C, RA-stat: the small-`b` piece from a box cover

`gammaSmallB_of_region` turns a `RegionPos` on the root box `[b0, b1] × [0, 1] × [σ0, 1]` into
`GammaSmallB S εc b1 σ0`, provided `2 · b0 ≤ S` (every admissible point has `b > S/2 ≥ b0`, because
`S < 2b - t d ≤ 2b`) and `b1 ≤ 9/20` (so the non-corner side condition `bσ ≤ 9/20` of `RegionPos` is automatic).
-/

namespace CKLaneC.RSCell

theorem gammaSmallB_of_region {S εc b0 b1 σ0 : ℝ} (hσ0 : 0 ≤ σ0) (hb1 : b1 ≤ 9 / 20) (hS : 2 * b0 ≤ S)
    (h : RegionPos b0 b1 0 1 σ0 1) : GammaSmallB S εc b1 σ0 := by
  intro b t d ht0 ht1 hd0 hdb _ hS' _ hbb1 hσ
  have hb0 : 0 < b := lt_trans hd0 hdb
  set σ := (b - d) / b with hσdef
  have hbσ : b * σ = b - d := by rw [hσdef]; field_simp
  have hd : b - b * σ = d := by rw [hbσ]; ring
  have hs0 : σ0 ≤ σ := by rw [hσdef, le_div_iff₀ hb0]; linarith
  have hs1 : σ < 1 := by rw [hσdef, div_lt_one hb0]; linarith
  have hu : b * σ ≤ 9 / 20 := by rw [hbσ]; linarith
  have htd : 0 ≤ t * d := mul_nonneg ht0 hd0.le
  have hbl : b0 ≤ b := by linarith
  have := h b t σ hbl hbb1 ht0 ht1 hs0 hs1.le hs1 hu
  rw [hd] at this
  exact this.le

end CKLaneC.RSCell

end


