-- Prove2me | Definitions.Def_CK_CKLaneM10_Leaf
-- name    : CK_CKLaneM10_Leaf
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:25:07.419028+00:00
-- url     : https://prove2.me/theorems/f9a1f4f1-3e50-4b22-849e-41f369717a78
-- title:
--   Courtade–Kumar proof module `CKLaneM10.Leaf` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM10.Leaf` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM10.Leaf` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM10.Leaf (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM10/Leaf.lean)

import Definitions.Def_CK_CKLaneM10_Checker

-- ===== source module CKLaneM10.Leaf =====
section

/-!
# Lane M10: certificate trees and binding to archived `(u, v, t)` leaves

* `checkFSTree_sound : checkFSTree B t = true → Sem B` (cells + exact box splits).
* `checkLeafFS p w = imageCheck (uvtBox p) w.box && checkFSTree w.box w.tree`; its soundness
  `checkLeafFS_sound : checkLeafFS p w = true → SemUVT (uvtBox p)` covers the FULL physical image of
  the archived leaf `p` (no entropy clipping; `CKLaneD.imageCheck` certifies `2^-u` bounds with
  exact `Nat` powers).
* `leaf_candidateGap_le_cost` / `leaf_gap_le_cost`: law-level conclusions with only the Boolean check,
  law membership in the exact leaf image and (for `μ.gap`) the psi-active branch condition.
-/

namespace CKLaneM10

open GeneralCK CKLaneD

/-- A certificate tree: a single feasible-split cell or an exact split of the box. -/
inductive FSTree where
  | cell (c : FSCell)
  | splitA (m : ℚ) (l r : FSTree)
  | splitB (m : ℚ) (l r : FSTree)
  | splitT (m : ℚ) (l r : FSTree)
  deriving Repr

def checkFSTree : Box → FSTree → Bool
  | B, .cell c => checkFS B c
  | B, .splitA m l r =>
      decide (B.alo ≤ m ∧ m ≤ B.ahi) && checkFSTree { B with ahi := m } l &&
        checkFSTree { B with alo := m } r
  | B, .splitB m l r =>
      decide (B.blo ≤ m ∧ m ≤ B.bhi) && checkFSTree { B with bhi := m } l &&
        checkFSTree { B with blo := m } r
  | B, .splitT m l r =>
      decide (B.t0 ≤ m ∧ m ≤ B.t1) && checkFSTree { B with t1 := m } l &&
        checkFSTree { B with t0 := m } r

theorem checkFSTree_sound : ∀ (B : Box) (t : FSTree), checkFSTree B t = true → Sem B
  | B, .cell c, h => checkFS_sound h
  | B, .splitA m l r, h => by
      simp only [checkFSTree, Bool.and_eq_true] at h
      exact sem_splitA (checkFSTree_sound _ l h.1.2) (checkFSTree_sound _ r h.2)
  | B, .splitB m l r, h => by
      simp only [checkFSTree, Bool.and_eq_true] at h
      exact sem_splitB (checkFSTree_sound _ l h.1.2) (checkFSTree_sound _ r h.2)
  | B, .splitT m l r, h => by
      simp only [checkFSTree, Bool.and_eq_true] at h
      exact sem_splitT (checkFSTree_sound _ l h.1.2) (checkFSTree_sound _ r h.2)

/-- A feasible-split witness: the rational box and its certificate tree. -/
structure FSWitness where
  box : Box
  tree : FSTree
  deriving Repr

/-- The Boolean method checker for one archived leaf path. -/
def checkLeafFS (p : List ℕ) (w : FSWitness) : Bool :=
  imageCheck (uvtBox p) w.box && checkFSTree w.box w.tree

/-- Unconditional semantic soundness: only `checkLeafFS p w = true`. -/
theorem checkLeafFS_sound {p : List ℕ} {w : FSWitness} (h : checkLeafFS p w = true) :
    SemUVT (uvtBox p) := by
  unfold checkLeafFS at h
  rw [Bool.and_eq_true] at h
  exact imageCheck_sound h.1 (checkFSTree_sound w.box w.tree h.2)

theorem checkLeavesFS_sound (L : List (List ℕ × FSWitness))
    (h : (L.all fun x => checkLeafFS x.1 x.2) = true) :
    ∀ x ∈ L, SemUVT (uvtBox x.1) := by
  intro x hx
  rw [List.all_eq_true] at h
  exact checkLeafFS_sound (h x hx)

/-- Law-level conclusion: psi candidate Bellman inequality on the exact leaf image. -/
theorem leaf_candidateGap_le_cost {p : List ℕ} {w : FSWitness} (hw : checkLeafFS p w = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hin : InUVT (uvtBox p) μ.a μ.b μ.meanEntropy) :
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost :=
  checkLeafFS_sound hw k μ hin

/-- Law-level conclusion for the hybrid gap on the psi-active branch. -/
theorem leaf_gap_le_cost {p : List ℕ} {w : FSWitness} (hw : checkLeafFS p w = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hin : InUVT (uvtBox p) μ.a μ.b μ.meanEntropy)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  (hybrid_gap_le_psi hact).trans (checkLeafFS_sound hw k μ hin)

/-- Owner form of a proved leaf statement. -/
theorem semUVT_gap_le_cost {U : UVT} (hU : SemUVT U) {k : ℕ} (μ : InteriorLaw (Fin k))
    (hin : InUVT U μ.a μ.b μ.meanEntropy)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  (hybrid_gap_le_psi hact).trans (hU k μ hin)

end CKLaneM10

end


