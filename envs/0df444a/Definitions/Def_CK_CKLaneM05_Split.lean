-- Prove2me | Definitions.Def_CK_CKLaneM05_Split
-- name    : CK_CKLaneM05_Split
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T00:12:31.885118+00:00
-- url     : https://prove2.me/theorems/2b7f8aa0-ff49-4483-860a-9651016b0758
-- title:
--   Courtade–Kumar proof module `CKLaneM05.Split` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM05.Split` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM05.Split` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM05.Split (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM05/Split.lean)

import Definitions.Def_CK_CKLaneM05_Checker

-- ===== source module CKLaneM05.Split =====
section

/-!
# Lane M05: exact halving of archived same-side boxes (subtree aggregation)

`ssBox (p ++ [d]) = ssStep (ssBox p) d`, and every law in `ssBox p` lies in one of the two halves
`ssBox (p ++ [2*ax])`, `ssBox (p ++ [2*ax+1])` (closed boxes, common face included). Hence parent
dominance on both halves gives parent dominance on the parent box.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05

open GeneralCK

theorem ssBox_append (p : List ℕ) (d : ℕ) : ssBox (p ++ [d]) = ssStep (ssBox p) d := by
  unfold ssBox
  rw [List.foldl_append]
  rfl

theorem inSSBox_split (B : SSBox) (ax : ℕ) (hax : ax < 3) {a b E : ℝ} (h : InSSBox B a b E) :
    InSSBox (ssStep B (2 * ax)) a b E ∨ InSSBox (ssStep B (2 * ax + 1)) a b E := by
  unfold InSSBox at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rcases (by omega : ax = 0 ∨ ax = 1 ∨ ax = 2) with rfl | rfl | rfl
  · rcases le_total (a / b) ((2 : ℝ) ^ (-((((B.x0 + B.x1) / 2 : ℚ)) : ℝ))) with hc | hc
    · right
      show (2 : ℝ) ^ (-(B.x1 : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-((((B.x0 + B.x1) / 2 : ℚ)) : ℝ)) ∧
        (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
        (B.t0 : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (B.t1 : ℝ) * ((H a + H b) / 2)
      exact ⟨h1, hc, h3, h4, h5, h6⟩
    · left
      show (2 : ℝ) ^ (-((((B.x0 + B.x1) / 2 : ℚ)) : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-(B.x0 : ℝ)) ∧
        (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
        (B.t0 : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (B.t1 : ℝ) * ((H a + H b) / 2)
      exact ⟨hc, h2, h3, h4, h5, h6⟩
  · rcases le_total b ((((B.b0 + B.b1) / 2 : ℚ)) : ℝ) with hc | hc
    · left
      show (2 : ℝ) ^ (-(B.x1 : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-(B.x0 : ℝ)) ∧
        (B.b0 : ℝ) ≤ b ∧ b ≤ ((((B.b0 + B.b1) / 2 : ℚ)) : ℝ) ∧
        (B.t0 : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (B.t1 : ℝ) * ((H a + H b) / 2)
      exact ⟨h1, h2, h3, hc, h5, h6⟩
    · right
      show (2 : ℝ) ^ (-(B.x1 : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-(B.x0 : ℝ)) ∧
        ((((B.b0 + B.b1) / 2 : ℚ)) : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
        (B.t0 : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (B.t1 : ℝ) * ((H a + H b) / 2)
      exact ⟨h1, h2, hc, h4, h5, h6⟩
  · rcases le_total E (((((B.t0 + B.t1) / 2 : ℚ)) : ℝ) * ((H a + H b) / 2)) with hc | hc
    · left
      show (2 : ℝ) ^ (-(B.x1 : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-(B.x0 : ℝ)) ∧
        (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
        (B.t0 : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ ((((B.t0 + B.t1) / 2 : ℚ)) : ℝ) * ((H a + H b) / 2)
      exact ⟨h1, h2, h3, h4, h5, hc⟩
    · right
      show (2 : ℝ) ^ (-(B.x1 : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-(B.x0 : ℝ)) ∧
        (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
        ((((B.t0 + B.t1) / 2 : ℚ)) : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (B.t1 : ℝ) * ((H a + H b) / 2)
      exact ⟨h1, h2, h3, h4, hc, h6⟩

/-- Parent dominance on both halves of an archived box gives it on the box. -/
theorem parentSem_split (p p0 p1 : List ℕ) (ax : ℕ) (hax : ax < 3)
    (e0 : p0 = p ++ [2 * ax]) (e1 : p1 = p ++ [2 * ax + 1])
    (h0 : ParentSem (ssBox p0)) (h1 : ParentSem (ssBox p1)) : ParentSem (ssBox p) := by
  subst e0 e1
  intro k μ hin
  rw [ssBox_append] at h0 h1
  rcases inSSBox_split (ssBox p) ax hax hin with h | h
  · exact h0 k μ h
  · exact h1 k μ h

end CKLaneM05

#check @CKLaneM05.parentSem_split
#print axioms CKLaneM05.parentSem_split

end


