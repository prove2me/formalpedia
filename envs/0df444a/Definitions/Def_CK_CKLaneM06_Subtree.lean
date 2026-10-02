-- Prove2me | Definitions.Def_CK_CKLaneM06_Subtree
-- name    : CK_CKLaneM06_Subtree
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T14:53:11.841864+00:00
-- url     : https://prove2.me/theorems/45e2d853-b35c-4e7a-8e81-10c6e147af25
-- title:
--   Courtade–Kumar proof module `CKLaneM06.Subtree` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.Subtree` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.Subtree` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.Subtree (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/Subtree.lean)

import Definitions.Def_CK_CKLaneM06_Semantics

-- ===== source module CKLaneM06.Subtree =====
section

/-!
# Lane M06: subtree aggregation over the archived exact-halving tree

`pathBox (p ++ [d]) = step (pathBox p) d`, and the two children `2a`, `2a+1` of a node cover its
box (closed halves).  Hence a method conclusion proved on both children holds on the parent box
(`ParentDominance.merge`); iterating gives the conclusion on every maximal archived subtree whose
leaves are all certified.
-/

set_option autoImplicit false

namespace CKLaneM06

theorem pathBox_append_single (p : List ℕ) (d : ℕ) : pathBox (p ++ [d]) = step (pathBox p) d := by
  simp only [pathBox, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The two archived children of a box cover it. -/
theorem Box.mem_step {B : Box} {x y z : ℝ} (h : B.Mem x y z) (a : ℕ) (ha : a < 3) :
    (step B (2 * a)).Mem x y z ∨ (step B (2 * a + 1)).Mem x y z := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rcases a with _ | _ | _ | a
  · show (step B 0).Mem x y z ∨ (step B 1).Mem x y z
    rcases le_total x (((B.lo0 + B.hi0) / 2 : ℚ) : ℝ) with hc | hc
    · exact Or.inl ⟨h1, hc, h3, h4, h5, h6⟩
    · exact Or.inr ⟨hc, h2, h3, h4, h5, h6⟩
  · show (step B 2).Mem x y z ∨ (step B 3).Mem x y z
    rcases le_total y (((B.lo1 + B.hi1) / 2 : ℚ) : ℝ) with hc | hc
    · exact Or.inl ⟨h1, h2, h3, hc, h5, h6⟩
    · exact Or.inr ⟨h1, h2, hc, h4, h5, h6⟩
  · show (step B 4).Mem x y z ∨ (step B 5).Mem x y z
    rcases le_total z (((B.lo2 + B.hi2) / 2 : ℚ) : ℝ) with hc | hc
    · exact Or.inl ⟨h1, h2, h3, h4, h5, hc⟩
    · exact Or.inr ⟨h1, h2, h3, h4, hc, h6⟩
  · omega

/-- Parent dominance on both archived children gives parent dominance on the parent box. -/
theorem ParentDominance.merge {p : List ℕ} {a : ℕ} (ha : a < 3)
    (h0 : ParentDominance (pathBox (p ++ [2 * a])))
    (h1 : ParentDominance (pathBox (p ++ [2 * a + 1]))) :
    ParentDominance (pathBox p) := by
  intro k μ hB
  rcases Box.mem_step hB a ha with h | h
  · exact h0 k μ (by rw [pathBox_append_single]; exact h)
  · exact h1 k μ (by rw [pathBox_append_single]; exact h)

end CKLaneM06

end


