-- Prove2me | Definitions.Def_CK_CKLaneA4_D2Base
-- name    : CK_CKLaneA4_D2Base
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:11:04.930552+00:00
-- url     : https://prove2.me/theorems/017a8c9a-d4af-43fe-8323-aa38d5b62a93
-- title:
--   Courtade–Kumar proof module `CKLaneA4.D2Base` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA4.D2Base` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA4.D2Base` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA4.D2Base (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA4/D2Base.lean)

import Definitions.Def_CK_CKLaneA_Cell

/-!
# Lane A4: Real-level cover combinators for Lane A's cell checker

`Covered u0 u1 r0 r1` is exactly the conclusion of Lane A's `CKLaneA.Cell.cellOK_sound` on the
rational box `[u0,u1] × [r0,r1]`.  Each certificate cell is proved by its OWN kernel evaluation
(`cellOK … = true := by decide +kernel`), and cells are glued by the two guillotine split lemmas
below, so no Boolean tree is ever evaluated in the kernel.
-/

namespace CKLaneA4.D2
open CKLaneA.Cell CKLaneA.Prog

/-- positivity of both program outputs (`D` and `m11` in probability-ratio coordinates) on a box -/
def Covered (u0 u1 r0 r1 : ℚ) : Prop :=
  ∀ ⦃a z : ℝ⦄, (u0 : ℝ) ≤ a → a ≤ (u1 : ℝ) → (r0 : ℝ) ≤ z → z ≤ (r1 : ℝ) →
    0 < r147_D a z ∧ 0 < r170_M a z

theorem covered_of_cellOK {u0 u1 r0 r1 : ℚ} {d : CellData} (h : cellOK u0 u1 r0 r1 d = true) :
    Covered u0 u1 r0 r1 := by
  intro a z h1 h2 h3 h4
  exact cellOK_sound h h1 h2 h3 h4

theorem covered_of_treeOK {u0 u1 r0 r1 : ℚ} {T : Tree} (h : treeOK u0 u1 r0 r1 T = true) :
    Covered u0 u1 r0 r1 := by
  intro a z h1 h2 h3 h4
  exact treeOK_sound T h h1 h2 h3 h4

theorem Covered.su {u0 u1 r0 r1 : ℚ} (m : ℚ) (hl : Covered u0 m r0 r1) (hr : Covered m u1 r0 r1) :
    Covered u0 u1 r0 r1 := by
  intro a z h1 h2 h3 h4
  rcases le_total a (m : ℝ) with h | h
  · exact hl h1 h h3 h4
  · exact hr h h2 h3 h4

theorem Covered.sr {u0 u1 r0 r1 : ℚ} (m : ℚ) (hl : Covered u0 u1 r0 m) (hr : Covered u0 u1 m r1) :
    Covered u0 u1 r0 r1 := by
  intro a z h1 h2 h3 h4
  rcases le_total z (m : ℝ) with h | h
  · exact hl h1 h2 h3 h
  · exact hr h1 h2 h h4

theorem Covered.apply {u0 u1 r0 r1 : ℚ} (h : Covered u0 u1 r0 r1) {a z : ℝ}
    (h1 : (u0 : ℝ) ≤ a) (h2 : a ≤ (u1 : ℝ)) (h3 : (r0 : ℝ) ≤ z) (h4 : z ≤ (r1 : ℝ)) :
    0 < r147_D a z ∧ 0 < r170_M a z := by
  unfold Covered at h
  exact h h1 h2 h3 h4

end CKLaneA4.D2


