-- Prove2me | Definitions.Def_CK_CKLaneG3_TreeCount
-- name    : CK_CKLaneG3_TreeCount
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:22:56.695761+00:00
-- url     : https://prove2.me/theorems/3eb96ffc-1318-4836-952b-b18b874cc17c
-- title:
--   Courtade–Kumar proof module `CKLaneG3.TreeCount` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.TreeCount` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.TreeCount` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.TreeCount (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/TreeCount.lean)

import Definitions.Def_CK_CKLaneG3_Families

-- ===== source module CKLaneG3.TreeCount =====
section

/-!
# Lane G3: label-only leaf counting on `PTree` (cheap kernel walks)

`tcount T = (T.leavesR rpre).length` and
`tcountLabel n T = ((T.leavesR rpre).filter (fun q => q.2 = n)).length`, so leaf / label counts of
large literal trees are decided by `decide +kernel` on a walk that builds no lists.
-/

namespace CKLaneG3

open CKLaneD

/-- Number of leaves. -/
def tcount : PTree → ℕ
  | .leaf _ => 1
  | .node _ l r => tcount l + tcount r

/-- Number of leaves with owner label `n`. -/
def tcountLabel (n : ℕ) : PTree → ℕ
  | .leaf l => if l = n then 1 else 0
  | .node _ l r => tcountLabel n l + tcountLabel n r

theorem tcount_eq : ∀ (T : PTree) (rpre : List ℕ), tcount T = (T.leavesR rpre).length
  | .leaf _, _ => by simp [tcount, PTree.leavesR]
  | .node ax l r, rpre => by
      simp only [tcount, PTree.leavesR, List.length_append]
      rw [tcount_eq l (2 * ax :: rpre), tcount_eq r ((2 * ax + 1) :: rpre)]

theorem tcountLabel_eq (n : ℕ) : ∀ (T : PTree) (rpre : List ℕ),
    tcountLabel n T = ((T.leavesR rpre).filter (fun q => q.2 = n)).length
  | .leaf l, _ => by
      by_cases h : l = n
      · simp [tcountLabel, PTree.leavesR, h]
      · simp [tcountLabel, PTree.leavesR, h]
  | .node ax l r, rpre => by
      simp only [tcountLabel, PTree.leavesR, List.filter_append, List.length_append]
      rw [tcountLabel_eq n l (2 * ax :: rpre), tcountLabel_eq n r ((2 * ax + 1) :: rpre)]

end CKLaneG3

end


