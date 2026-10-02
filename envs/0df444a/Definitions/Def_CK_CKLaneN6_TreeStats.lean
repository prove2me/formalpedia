-- Prove2me | Definitions.Def_CK_CKLaneN6_TreeStats
-- name    : CK_CKLaneN6_TreeStats
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:00:34.386038+00:00
-- url     : https://prove2.me/theorems/7baf42ef-495c-4a0f-a5fe-aeb4fbe618aa
-- title:
--   Courtade–Kumar proof module `CKLaneN6.TreeStats` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.TreeStats` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.TreeStats` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.TreeStats (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/TreeStats.lean)

import Definitions.Def_CK_CKLaneN6_TreeBase

-- ===== source module CKLaneN6.TreeStats =====
section

/-!
# Lane N6: structural statistics of partition trees

`numLeaves`, `countLabel` are computed by structural recursion without building paths, and agree with
the leaf list: `leaves_length`, `leaves_countLabel`.  They make leaf/label counts of the 76,547-leaf archived
tree cheap to certify by `decide +kernel`.
-/

set_option autoImplicit false

namespace CKLaneN6

def PTree.numLeaves : PTree → ℕ
  | .leaf _ => 1
  | .node _ l r => l.numLeaves + r.numLeaves

def PTree.countLabel (c : ℕ) : PTree → ℕ
  | .leaf l => if l = c then 1 else 0
  | .node _ l r => l.countLabel c + r.countLabel c

theorem PTree.leavesR_length : ∀ (T : PTree) (rpre : List ℕ), (T.leavesR rpre).length = T.numLeaves
  | .leaf _, _ => rfl
  | .node ax l r, rpre => by
      simp only [PTree.leavesR, PTree.numLeaves, List.length_append, PTree.leavesR_length l,
        PTree.leavesR_length r]

theorem PTree.leaves_length (T : PTree) : T.leaves.length = T.numLeaves := T.leavesR_length []

theorem PTree.leavesR_countLabel (c : ℕ) : ∀ (T : PTree) (rpre : List ℕ),
    ((T.leavesR rpre).filter (fun x => x.2 = c)).length = T.countLabel c
  | .leaf l, _ => by
      by_cases h : l = c
      · simp [PTree.leavesR, PTree.countLabel, h]
      · simp [PTree.leavesR, PTree.countLabel, h]
  | .node ax l r, rpre => by
      simp only [PTree.leavesR, PTree.countLabel, List.filter_append, List.length_append,
        PTree.leavesR_countLabel c l, PTree.leavesR_countLabel c r]

theorem PTree.leaves_countLabel (T : PTree) (c : ℕ) :
    (T.leaves.filter (fun x => x.2 = c)).length = T.countLabel c := T.leavesR_countLabel c []

end CKLaneN6

end


