-- Prove2me | Definitions.Def_CK_CKLaneA1_SplitLemmas
-- name    : CK_CKLaneA1_SplitLemmas
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:41:11.756989+00:00
-- url     : https://prove2.me/theorems/46aed543-6aad-494f-83f8-6de82b0137b5
-- title:
--   Courtade–Kumar proof module `CKLaneA1 (split glue lemmas)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1 (split glue lemmas)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1 (split glue lemmas)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1 (split glue lemmas) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1 (split glue lemmas).lean)

import Definitions.Def_CK_CKLaneA1_FEStrip
import Definitions.Def_CK_CKLaneA1_BSCover

/-! Glue lemmas used to split the generated `CKLaneA1` cover chunks (one large kernel
check each) into several smaller kernel checks. They only restate how the source's
Boolean checkers `cellsCheck` / `bsCellsCheck` evaluate a concatenated cell list. -/

set_option autoImplicit false

namespace CKLaneA1

theorem cellsCheck_append (n : ℕ) (L2 : DI) (s : FEStrip) : ∀ (A : Node) (l1 l2 : List FECell),
    cellsCheck n L2 s A (l1 ++ l2) = (cellsCheck n L2 s A l1 && cellsCheck n L2 s (lastNode A l1) l2)
  | A, [], l2 => by simp [cellsCheck, lastNode]
  | A, c :: l1, l2 => by
      simp only [List.cons_append, cellsCheck, lastNode, cellsCheck_append n L2 s c.w l1 l2, Bool.and_assoc]

theorem cellsCheck_geom (n : ℕ) (L2 : DI) (u1 u2 w0 : Node) (cs : List FECell) :
    ∀ (A : Node) (l : List FECell),
    cellsCheck n L2 ⟨u1, u2, w0, cs⟩ A l = cellsCheck n L2 ⟨u1, u2, w0, []⟩ A l
  | A, [] => rfl
  | A, c :: l => by
      have h : cellCheck n L2 ⟨u1, u2, w0, cs⟩ A c.w c.cd = cellCheck n L2 ⟨u1, u2, w0, []⟩ A c.w c.cd := rfl
      simp only [cellsCheck, h, cellsCheck_geom n L2 u1 u2 w0 cs c.w l]

theorem stripOK_of_parts {n : ℕ} {L2 : DI} (s : FEStrip)
    (hhead : (stripOKu n L2 s && nodeOK s.w0 && decide (40 * s.w0.xa ≤ SCz) &&
      decide ((lastNode s.w0 s.cells).xa = SCz / 2) && decide (s.cells ≠ [])) = true)
    (hcells : cellsCheck n L2 s s.w0 s.cells = true) : stripOK n L2 s = true := by
  unfold stripOK; rw [hhead, hcells]; rfl

theorem bsCellsCheck_append (n : ℕ) (L2 : DI) (s : BSStrip) : ∀ (A : RNode) (l1 l2 : List BSCell),
    bsCellsCheck n L2 s A (l1 ++ l2) = (bsCellsCheck n L2 s A l1 && bsCellsCheck n L2 s (rLast A l1) l2)
  | A, [], l2 => by simp [bsCellsCheck, rLast]
  | A, c :: l1, l2 => by
      simp only [List.cons_append, bsCellsCheck, rLast, bsCellsCheck_append n L2 s c.r l1 l2, Bool.and_assoc]

theorem bsCellsCheck_geom (n : ℕ) (L2 : DI) (w1 w2 : Node) (cs : List BSCell) :
    ∀ (A : RNode) (l : List BSCell),
    bsCellsCheck n L2 ⟨w1, w2, cs⟩ A l = bsCellsCheck n L2 ⟨w1, w2, []⟩ A l
  | A, [] => rfl
  | A, c :: l => by
      have h : bsCellCheck n L2 ⟨w1, w2, cs⟩ A c.r c.two c.cd = bsCellCheck n L2 ⟨w1, w2, []⟩ A c.r c.two c.cd := rfl
      simp only [bsCellsCheck, h, bsCellsCheck_geom n L2 w1 w2 cs c.r l]

theorem bsStripFull_of_parts {n : ℕ} {L2 : DI} (s : BSStrip)
    (hhead : (bsStripOK n L2 s && decide (s.cells ≠ []) && decide ((rLast r0 s.cells).ra = SCz)) = true)
    (hcells : bsCellsCheck n L2 s r0 s.cells = true) : bsStripFull n L2 s = true := by
  unfold bsStripFull; rw [hhead, hcells]; rfl

end CKLaneA1


