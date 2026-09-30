-- Prove2me | Definitions.Def_CK_CKLaneD_ArchTree_part00
-- name    : CK_CKLaneD_ArchTree_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:45:53.087024+00:00
-- url     : https://prove2.me/theorems/f09aec96-a826-436d-86e2-22a1a668af9b
-- title:
--   Courtade–Kumar proof module `CKLaneD.ArchTree (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneD.ArchTree (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneD.ArchTree (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneD.ArchTree (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneD/ArchTree (part 1 of 3).lean)

import Definitions.Def_CK_CKLaneD_FleetBase

/-!
# The archived outer-opposite partition tree

Generated from `OUTER_OPPOSITE_RESULT.json` (sha256 44344386e10adb6f6bdd066d7fbe4056ab2c10164019c0d9dce378a2e9edf72d) by
`work/gen_tree.py`: all 29495 leaves with owner labels
0 = endpoint_plane_taylor, 1 = shifted_logsum, 2 = global_cap_slope, 3 = global_feasible_split, 4 = global_eight_ratio, 5 = outside, 6 = global_parent_envelope, 7 = global_parent8, 8 = global_low_entropy_025, 9 = global_parent16, 10 = global_parent_direct, 11 = logsum_direct, 12 = global_corner.
A node `N ax l r` halves axis `ax` (0 = u, 1 = v, 2 = t); `l` is the lower half (digit `2 ax`),
`r` the upper half (digit `2 ax + 1`), exactly as `OUTER_OPPOSITE.reconstruct`.
-/

namespace CKLaneD

inductive PTree where
  | leaf (label : ℕ)
  | node (axis : ℕ) (l r : PTree)
  deriving Repr

/-- All leaves `(path, label)` of a tree; `rpre` is the REVERSED path prefix. -/
def PTree.leavesR : PTree → List ℕ → List (List ℕ × ℕ)
  | .leaf l, rpre => [(rpre.reverse, l)]
  | .node ax l r, rpre => PTree.leavesR l (2 * ax :: rpre) ++ PTree.leavesR r ((2 * ax + 1) :: rpre)

/-- All leaves `(path, label)` of a tree (paths from the root). -/
def PTree.leaves (T : PTree) : List (List ℕ × ℕ) := T.leavesR []

namespace ArchTree

local notation "L" => PTree.leaf
local notation "N" => PTree.node


end ArchTree

end CKLaneD


