-- Prove2me | Definitions.Def_CK_CKLaneM10_Leaves_q01
-- name    : CK_CKLaneM10_Leaves_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T01:34:20.398063+00:00
-- url     : https://prove2.me/theorems/63f8ad9d-524a-4c36-9cb3-ab0b5d7b6d33
-- title:
--   Courtade–Kumar proof module `CKLaneM10.Leaves (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM10.Leaves (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM10.Leaves (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM10.Leaves (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM10/Leaves (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneM10_Leaves_q00

namespace CKLaneM10.Leaves
open CKLaneD CKLaneM10
/-- The archived `global_feasible_split` leaf paths (label 3), in archive order. -/
def fsPaths : List (List ℕ) :=
  (ArchTree.archTree.leaves.filter (fun x => x.2 = 3)).map Prod.fst

theorem fsPaths_eq : fsPaths = allLeaves.map Prod.fst := by decide +kernel

theorem allLeaves_length : allLeaves.length = 1872 := by decide +kernel

end CKLaneM10.Leaves


