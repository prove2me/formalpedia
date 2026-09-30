-- Prove2me | Definitions.Def_CK_CKLaneC_RSCell_Union
-- name    : CK_CKLaneC_RSCell_Union
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:35:54.053416+00:00
-- url     : https://prove2.me/theorems/f7d3917b-bcbe-4868-8f36-4d1d6c7012a1
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSCell.Union` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSCell.Union` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSCell.Union` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSCell.Union (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSCell/Union.lean)

import Definitions.Def_CK_CKLaneN23_RSDefs

-- ===== source module CKLaneC.RSCell.Union =====
section

/-!
# Lane C, RA-stat: region split of `GammaNonCorner` (the union theorem consumed by N23b)

The split follows the coordinator's decision of 07:10Z:
* `GammaUTail S εc σ0` is owned by Lane R2. It covers all `b` with `u = b - d ≤ σ0 · b`.
* `GammaSmallB S εc b1 σ0` is owned by Lane C (v-mode contacts). It covers `b ≤ b1` with `σ0 · b ≤ u`.
* `GammaBulk S εc b1 σ0` is owned by Lane C (TM cell cover). It covers `b1 ≤ b` with `σ0 · b ≤ u`.

Each piece carries all hypotheses of `GammaNonCorner` plus its region restriction. The pieces overlap at equality.
-/

namespace CKLaneC.RSCell

open CKLaneN23.RS

/-- `u`-tail piece (Lane R2): `u = b - d ≤ σ0 · b`, all `b`. -/
def GammaUTail (S εc σ0 : ℝ) : Prop :=
  ∀ b t d : ℝ, 0 ≤ t → t ≤ 1 → 0 < d → d < b → b ≤ 1 / 2 → S < 2 * b - t * d → εc ≤ (1 / 2 - b) + d →
    b - d ≤ σ0 * b → 0 ≤ rayGamma b t d

/-- Small-`b` piece (Lane C): `b ≤ b1`, `σ0 · b ≤ u`. -/
def GammaSmallB (S εc b1 σ0 : ℝ) : Prop :=
  ∀ b t d : ℝ, 0 ≤ t → t ≤ 1 → 0 < d → d < b → b ≤ 1 / 2 → S < 2 * b - t * d → εc ≤ (1 / 2 - b) + d →
    b ≤ b1 → σ0 * b ≤ b - d → 0 ≤ rayGamma b t d

/-- Bulk piece (Lane C): `b1 ≤ b`, `σ0 · b ≤ u`. -/
def GammaBulk (S εc b1 σ0 : ℝ) : Prop :=
  ∀ b t d : ℝ, 0 ≤ t → t ≤ 1 → 0 < d → d < b → b ≤ 1 / 2 → S < 2 * b - t * d → εc ≤ (1 / 2 - b) + d →
    b1 ≤ b → σ0 * b ≤ b - d → 0 ≤ rayGamma b t d

/-- The union: the three pieces give `GammaNonCorner`. -/
theorem gammaNonCorner_of_pieces {S εc b1 σ0 : ℝ} (hu : GammaUTail S εc σ0) (hs : GammaSmallB S εc b1 σ0)
    (hb : GammaBulk S εc b1 σ0) : GammaNonCorner S εc := by
  intro b t d ht0 ht1 hd0 hdb hb12 hS hεc
  rcases le_total (b - d) (σ0 * b) with h2 | h2
  · exact hu b t d ht0 ht1 hd0 hdb hb12 hS hεc h2
  · rcases le_total b b1 with h1 | h1
    · exact hs b t d ht0 ht1 hd0 hdb hb12 hS hεc h1 h2
    · exact hb b t d ht0 ht1 hd0 hdb hb12 hS hεc h1 h2

end CKLaneC.RSCell

end


