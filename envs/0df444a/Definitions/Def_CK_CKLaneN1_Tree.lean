-- Prove2me | Definitions.Def_CK_CKLaneN1_Tree
-- name    : CK_CKLaneN1_Tree
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:50:29.289986+00:00
-- url     : https://prove2.me/theorems/074ba50a-fca4-46b9-b9bf-b042a1097b31
-- title:
--   Courtade–Kumar proof module `CKLaneN1.Tree` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.Tree` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.Tree` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.Tree (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/Tree.lean)

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- ===== source module CKLaneN1.Tree =====
section

set_option autoImplicit false

/-!
# Lane N1: generic archived binary partition trees over rational boxes

Paths use the archive encoding: digit `c` halves axis `c / 2`, keeping the lower half for even `c`
and the upper half for odd `c` (exact midpoint, `reconstruct` in every archived checker).
`PT.cover`: every real point of the root box lies in the box of some leaf of any tree.
-/

namespace CKLaneN1

/-- Compact dyadic literal `n / 2^e`. -/
def dy (n : ℤ) (e : ℕ) : ℚ := (n : ℚ) / ((2 ^ e : ℕ) : ℚ)

/-- A binary partition tree with leaf payloads (`node ax l r` halves axis `ax`). -/
inductive PT (α : Type) where
  | leaf (d : α)
  | node (axis : ℕ) (l r : PT α)
  deriving Repr

/-- All leaves `(path, payload)`; `rpre` is the reversed path prefix. -/
def PT.leavesR {α : Type} : PT α → List ℕ → List (List ℕ × α)
  | .leaf d, rpre => [(rpre.reverse, d)]
  | .node ax l r, rpre => l.leavesR (2 * ax :: rpre) ++ r.leavesR ((2 * ax + 1) :: rpre)

def PT.leaves {α : Type} (T : PT α) : List (List ℕ × α) := T.leavesR []

/-- A rational box in three coordinates (a 2-D box uses a degenerate third coordinate). -/
structure B3 where
  a0 : ℚ
  a1 : ℚ
  b0 : ℚ
  b1 : ℚ
  c0 : ℚ
  c1 : ℚ
  deriving Repr, DecidableEq

/-- One exact halving step (archive `split`). -/
def B3.step (B : B3) : ℕ → B3
  | 0 => { B with a1 := (B.a0 + B.a1) / 2 }
  | 1 => { B with a0 := (B.a0 + B.a1) / 2 }
  | 2 => { B with b1 := (B.b0 + B.b1) / 2 }
  | 3 => { B with b0 := (B.b0 + B.b1) / 2 }
  | 4 => { B with c1 := (B.c0 + B.c1) / 2 }
  | 5 => { B with c0 := (B.c0 + B.c1) / 2 }
  | _ => B

/-- The exact leaf box of a path from the root `R`. -/
def B3.ofPath (R : B3) (p : List ℕ) : B3 := p.foldl B3.step R

/-- Membership of a real point. -/
def B3.Mem (B : B3) (x y z : ℝ) : Prop :=
  (B.a0 : ℝ) ≤ x ∧ x ≤ (B.a1 : ℝ) ∧ (B.b0 : ℝ) ≤ y ∧ y ≤ (B.b1 : ℝ) ∧
    (B.c0 : ℝ) ≤ z ∧ z ≤ (B.c1 : ℝ)

theorem B3.ofPath_append (R : B3) (p : List ℕ) (d : ℕ) :
    R.ofPath (p ++ [d]) = (R.ofPath p).step d := by
  unfold B3.ofPath
  rw [List.foldl_append]
  rfl

theorem B3.mem_step {B : B3} {x y z : ℝ} (h : B.Mem x y z) (ax : ℕ) :
    (B.step (2 * ax)).Mem x y z ∨ (B.step (2 * ax + 1)).Mem x y z := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rcases ax with _ | _ | _ | ax
  · rcases le_total x (((B.a0 + B.a1) / 2 : ℚ) : ℝ) with hm | hm
    · left; exact ⟨h1, hm, h3, h4, h5, h6⟩
    · right; exact ⟨hm, h2, h3, h4, h5, h6⟩
  · rcases le_total y (((B.b0 + B.b1) / 2 : ℚ) : ℝ) with hm | hm
    · left; exact ⟨h1, h2, h3, hm, h5, h6⟩
    · right; exact ⟨h1, h2, hm, h4, h5, h6⟩
  · rcases le_total z (((B.c0 + B.c1) / 2 : ℚ) : ℝ) with hm | hm
    · left; exact ⟨h1, h2, h3, h4, h5, hm⟩
    · right; exact ⟨h1, h2, h3, h4, hm, h6⟩
  · left
    have e : 2 * (ax + 3) = 2 * ax + 6 := by ring
    simp only [B3.step, e]
    exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem PT.coverR {α : Type} (R : B3) : ∀ (T : PT α) (rpre : List ℕ) {x y z : ℝ},
    (R.ofPath rpre.reverse).Mem x y z → ∃ q ∈ T.leavesR rpre, (R.ofPath q.1).Mem x y z
  | .leaf d, rpre, x, y, z, h => ⟨(rpre.reverse, d), by simp [PT.leavesR], h⟩
  | .node ax l r, rpre, x, y, z, h => by
      rcases B3.mem_step h ax with h' | h'
      · rw [← B3.ofPath_append, ← List.reverse_cons] at h'
        obtain ⟨q, hq, hq'⟩ := PT.coverR R l (2 * ax :: rpre) h'
        exact ⟨q, by simp only [PT.leavesR, List.mem_append]; exact Or.inl hq, hq'⟩
      · rw [← B3.ofPath_append, ← List.reverse_cons] at h'
        obtain ⟨q, hq, hq'⟩ := PT.coverR R r ((2 * ax + 1) :: rpre) h'
        exact ⟨q, by simp only [PT.leavesR, List.mem_append]; exact Or.inr hq, hq'⟩

/-- Every point of the root box lies in the box of some leaf. -/
theorem PT.cover {α : Type} (R : B3) (T : PT α) {x y z : ℝ} (h : R.Mem x y z) :
    ∃ q ∈ T.leaves, (R.ofPath q.1).Mem x y z :=
  PT.coverR R T [] h

/-- Boolean: every leaf satisfies `f`. -/
def PT.allLeaves {α : Type} (f : List ℕ → α → Bool) (T : PT α) : Bool :=
  T.leaves.all (fun q => f q.1 q.2)

theorem PT.allLeaves_sound {α : Type} {f : List ℕ → α → Bool} {T : PT α}
    (h : T.allLeaves f = true) : ∀ q ∈ T.leaves, f q.1 q.2 = true := by
  intro q hq
  unfold PT.allLeaves at h
  exact List.all_eq_true.mp h q hq

end CKLaneN1

end


