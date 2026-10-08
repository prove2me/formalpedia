-- Prove2me | Definitions.Def_CK_CKLaneN6_TreeCover
-- name    : CK_CKLaneN6_TreeCover
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T05:49:27.683214+00:00
-- url     : https://prove2.me/theorems/9054064d-2a3c-4bbc-9e01-0d9d750bf538
-- title:
--   Courtade–Kumar proof module `CKLaneN6.TreeCover` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.TreeCover` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.TreeCover` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.TreeCover (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/TreeCover.lean)

import Definitions.Def_CK_CKLaneN6_Tree

-- ===== source module CKLaneN6.TreeCover =====
section

/-!
# Lane N6: coverage of the Thm 3 row by the archived partition tree

`archTree_cover`: every interior law with `a ≤ b`, `1/10 ≤ a`, `b ≤ 1/2`, `10^-6 ≤ E` (in particular every
law of `CKLaneN23.SmallRatioT3NearRest`) lies in the exact box `CKLaneM05.FE8.feBox q.1` of some leaf `q`
(any label) of the archived tree.  `row_of_all_leaves`: the Thm 3 obligation on every leaf gives the row.
-/

set_option autoImplicit false

namespace CKLaneN6

open GeneralCK CKLaneM05.FE8 CKLaneN6.ArchTree

theorem archTree_wf : archTree.wf = true := by decide +kernel

theorem archTree_cover {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b) (ha : 1 / 10 ≤ μ.a)
    (hb : μ.b ≤ 1 / 2) (hE : 1 / 1000000 ≤ μ.meanEntropy) :
    ∃ q ∈ archTree.leaves, CKLaneD.InBox (feBox q.1) μ.a μ.b μ.meanEntropy :=
  PTree.cover archTree archTree_wf (inBox_feRoot μ hab ha hb hE)

theorem row_of_all_leaves (h : ∀ q ∈ archTree.leaves, LeafOK (feBox q.1)) :
    CKLaneN23.SmallRatioT3NearRest :=
  PTree.row_of_leaves archTree archTree_wf h

end CKLaneN6

end


