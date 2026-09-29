-- Prove2me | Definitions.Def_CK_CKLaneA5_Join
-- name    : CK_CKLaneA5_Join
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:06:31.556361+00:00
-- url     : https://prove2.me/theorems/f862ebfd-e1a3-4a78-881b-74c1436c635d
-- title:
--   Courtade–Kumar proof module `CKLaneA5.Join` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA5.Join` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA5.Join` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA5.Join (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA5/Join.lean)

import Definitions.Def_CK_CKLaneA_Cell

/-!
# Lane A5: join lemmas for Lane A's guillotine-tree checker `CKLaneA.Cell.treeOK`

Verbatim copy (namespace renamed `CKLaneA2` → `CKLaneA5`) of Lane A2's `CKLaneA2/Join.lean`.
Each certificate cell is checked in its own declaration (`decide +kernel`, fresh kernel cache);
internal tree nodes are assembled with these two lemmas, whose split side conditions are
closed by `decide +kernel` on rational literals.
-/

namespace CKLaneA5
open CKLaneA.Cell

theorem treeOK_su {u0 u1 r0 r1 m : ℚ} {l r : Tree}
    (hm : (decide (u0 ≤ m) && decide (m ≤ u1)) = true)
    (hl : treeOK u0 m r0 r1 l = true) (hr : treeOK m u1 r0 r1 r = true) :
    treeOK u0 u1 r0 r1 (.su m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

theorem treeOK_sr {u0 u1 r0 r1 m : ℚ} {l r : Tree}
    (hm : (decide (r0 ≤ m) && decide (m ≤ r1)) = true)
    (hl : treeOK u0 u1 r0 m l = true) (hr : treeOK u0 u1 m r1 r = true) :
    treeOK u0 u1 r0 r1 (.sr m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

end CKLaneA5


