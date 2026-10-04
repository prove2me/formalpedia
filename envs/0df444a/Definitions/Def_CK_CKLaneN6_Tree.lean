-- Prove2me | Definitions.Def_CK_CKLaneN6_Tree
-- name    : CK_CKLaneN6_Tree
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:06:16.756986+00:00
-- url     : https://prove2.me/theorems/b34cb783-1b11-4bef-bd98-7ba44692bca8
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Tree` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Tree` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Tree` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Tree (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Tree.lean)

import Definitions.Def_CK_CKLaneN6_TreeA
import Definitions.Def_CK_CKLaneN6_TreeB
import Definitions.Def_CK_CKLaneN6_TreeC
import Definitions.Def_CK_CKLaneN6_TreeD
import Definitions.Def_CK_CKLaneN6_TreeE
import Definitions.Def_CK_CKLaneN6_TreeF
import Definitions.Def_CK_CKLaneN6_TreeStats

-- ===== source module CKLaneN6.Tree =====
section

/-!
# Lane N6: the archived SMALL_RATIO Thm 3 partition tree (76,547 labelled leaves)

Exact binary tree re-derived from the leaf paths of `SMALL_DIFFERENCE_RESULT.json` (sha256
b7d88a1381e72330e32efbb3bd07379246aeac763aac818fdada7c396f3214a2).
A node `N ax l r` halves axis `ax` (0 = a, 1 = b, 2 = t): `l` is digit `2 ax`, `r` digit `2 ax + 1`,
exactly as `FULL_ENTROPY_COVER.reconstruct`.  The top six levels are the archive's shard roots
(axis = depth mod 3).  Label codes: 0 = outside, 1 = prior_same_side, 2 = central_small_ratio, 3 = cap, 4 = phi_parent, 5 = phi_parent_log, 6 = sum_normalized, 7 = endpoint_sum, 8 = logsum, 9 = logsum_quadratic, 10 = logsum_quad_endpoints, 11 = shifted_logsum, 12 = endpoint_plane_endpoints, 13 = endpoint_plane_taylor.
Leaf and label counts are certified by structural recursion (`CKLaneN6.TreeStats`).
-/

namespace CKLaneN6.ArchTree

local notation "L" => PTree.leaf
local notation "N" => PTree.node

/-- The archived partition tree (root `[1/10,1/2]² × [0,1]` in `(a, b, t)`). -/
def archTree : PTree :=
  (N 0 (N 1 (N 2 (N 0 (N 1 (N 2 t024024 t024025) (N 2 t024034 t024035)) (N 1 (N 2 t024124 t024125) (N 2 t024134 t024135))) (N 0 (N 1 (N 2 t025024 t025025) (N 2 t025034 t025035)) (N 1 (N 2 t025124 t025125) (N 2 t025134 t025135)))) (N 2 (N 0 (N 1 (N 2 t034024 t034025) (N 2 t034034 t034035)) (N 1 (N 2 t034124 t034125) (N 2 t034134 t034135))) (N 0 (N 1 (N 2 t035024 t035025) (N 2 t035034 t035035)) (N 1 (N 2 t035124 t035125) (N 2 t035134 t035135))))) (N 1 (N 2 (N 0 (N 1 (N 2 t124024 t124025) (N 2 t124034 t124035)) (N 1 (N 2 t124124 t124125) (N 2 t124134 t124135))) (N 0 (N 1 (N 2 t125024 t125025) (N 2 t125034 t125035)) (N 1 (N 2 t125124 t125125) (N 2 t125134 t125135)))) (N 2 (N 0 (N 1 (N 2 t134024 t134025) (N 2 t134034 t134035)) (N 1 (N 2 t134124 t134125) (N 2 t134134 t134135))) (N 0 (N 1 (N 2 t135024 t135025) (N 2 t135034 t135035)) (N 1 (N 2 t135124 t135125) (N 2 t135134 t135135))))))

theorem archTree_numLeaves : archTree.numLeaves = 76547 := by decide +kernel

theorem archTree_leaf_count : archTree.leaves.length = 76547 := by
  rw [PTree.leaves_length]; exact archTree_numLeaves

theorem count_outside : (archTree.leaves.filter (fun x => x.2 = 0)).length = 1923 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_prior_same_side : (archTree.leaves.filter (fun x => x.2 = 1)).length = 1599 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_central_small_ratio : (archTree.leaves.filter (fun x => x.2 = 2)).length = 68 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_cap : (archTree.leaves.filter (fun x => x.2 = 3)).length = 962 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_phi_parent : (archTree.leaves.filter (fun x => x.2 = 4)).length = 16761 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_phi_parent_log : (archTree.leaves.filter (fun x => x.2 = 5)).length = 1582 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_sum_normalized : (archTree.leaves.filter (fun x => x.2 = 6)).length = 31693 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_endpoint_sum : (archTree.leaves.filter (fun x => x.2 = 7)).length = 939 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_logsum : (archTree.leaves.filter (fun x => x.2 = 8)).length = 6986 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_logsum_quadratic : (archTree.leaves.filter (fun x => x.2 = 9)).length = 1401 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_logsum_quad_endpoints : (archTree.leaves.filter (fun x => x.2 = 10)).length = 2908 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_shifted_logsum : (archTree.leaves.filter (fun x => x.2 = 11)).length = 2423 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_endpoint_plane_endpoints : (archTree.leaves.filter (fun x => x.2 = 12)).length = 929 := by
  rw [PTree.leaves_countLabel]; decide +kernel

theorem count_endpoint_plane_taylor : (archTree.leaves.filter (fun x => x.2 = 13)).length = 6373 := by
  rw [PTree.leaves_countLabel]; decide +kernel

end CKLaneN6.ArchTree

end


