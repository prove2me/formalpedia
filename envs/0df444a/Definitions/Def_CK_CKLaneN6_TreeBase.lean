-- Prove2me | Definitions.Def_CK_CKLaneN6_TreeBase
-- name    : CK_CKLaneN6_TreeBase
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:57:05.939785+00:00
-- url     : https://prove2.me/theorems/84663a66-1e21-472a-99bb-ab6665a7850f
-- title:
--   Courtade–Kumar proof module `CKLaneN6.TreeBase` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.TreeBase` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.TreeBase` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.TreeBase (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/TreeBase.lean)

import Definitions.Def_CK_CKLaneN6_Base

-- ===== source module CKLaneN6.TreeBase =====
section

/-!
# Lane N6: labelled partition trees over the archived Thm 3 root and their coverage

`PTree`: `leaf label` | `node axis l r` (`l` = digit `2 axis`, `r` = digit `2 axis + 1`, exact
halving `CKLaneM05.FE8.feStep`).  `PTree.cover`: for a tree whose node axes are `< 3`, every point of
the root box lies in the box of some leaf (any label).  `PTree.sound`: the Thm 3 obligation on all
leaves gives it on the root box.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN6

open CKLaneM05.FE8 (feRoot feStep feBox feBox_append inBox_step)

inductive PTree where
  | leaf (label : ℕ)
  | node (axis : ℕ) (l r : PTree)
  deriving Repr

/-- All leaves `(path, label)`; `rpre` is the REVERSED path prefix. -/
def PTree.leavesR : PTree → List ℕ → List (List ℕ × ℕ)
  | .leaf l, rpre => [(rpre.reverse, l)]
  | .node ax l r, rpre => PTree.leavesR l (2 * ax :: rpre) ++ PTree.leavesR r ((2 * ax + 1) :: rpre)

/-- All leaves `(path, label)` of a tree (paths from the root). -/
def PTree.leaves (T : PTree) : List (List ℕ × ℕ) := T.leavesR []

/-- Every node halves one of the three coordinates. -/
def PTree.wf : PTree → Bool
  | .leaf _ => true
  | .node ax l r => decide (ax < 3) && l.wf && r.wf

theorem PTree.coverR : ∀ (T : PTree) (rpre : List ℕ), T.wf = true → ∀ {a b E : ℝ},
    CKLaneD.InBox (feBox rpre.reverse) a b E → ∃ q ∈ T.leavesR rpre, CKLaneD.InBox (feBox q.1) a b E
  | .leaf l, rpre, _, a, b, E, h => ⟨(rpre.reverse, l), by simp [PTree.leavesR], h⟩
  | .node ax l r, rpre, hw, a, b, E, h => by
      simp only [PTree.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
      obtain ⟨⟨hax, hl⟩, hr⟩ := hw
      rcases inBox_step _ ax hax h with h' | h'
      · rw [← feBox_append, ← List.reverse_cons] at h'
        obtain ⟨q, hq, hq'⟩ := PTree.coverR l (2 * ax :: rpre) hl h'
        exact ⟨q, by simp only [PTree.leavesR, List.mem_append]; exact Or.inl hq, hq'⟩
      · rw [← feBox_append, ← List.reverse_cons] at h'
        obtain ⟨q, hq, hq'⟩ := PTree.coverR r ((2 * ax + 1) :: rpre) hr h'
        exact ⟨q, by simp only [PTree.leavesR, List.mem_append]; exact Or.inr hq, hq'⟩

/-- Coverage: every point of the root box lies in some leaf box. -/
theorem PTree.cover (T : PTree) (hT : T.wf = true) {a b E : ℝ}
    (h : CKLaneD.InBox feRoot a b E) : ∃ q ∈ T.leaves, CKLaneD.InBox (feBox q.1) a b E :=
  PTree.coverR T [] hT (by simpa [feBox] using h)

/-- The row from the obligation on every leaf of a well-formed tree. -/
theorem PTree.row_of_leaves (T : PTree) (hT : T.wf = true)
    (h : ∀ q ∈ T.leaves, LeafOK (feBox q.1)) : CKLaneN23.SmallRatioT3NearRest := by
  intro k μ hab hsum ha hb hd hd20 hE hor hs hact
  obtain ⟨q, hq, hin⟩ := PTree.cover T hT (CKLaneM05.FE8.inBox_feRoot μ hab ha hb hE)
  exact h q hq k μ hab hsum ha hb hd hd20 hE hor hs hin hact

end CKLaneN6

end


