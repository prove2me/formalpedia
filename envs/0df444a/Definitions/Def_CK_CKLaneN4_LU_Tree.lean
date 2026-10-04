-- Prove2me | Definitions.Def_CK_CKLaneN4_LU_Tree
-- name    : CK_CKLaneN4_LU_Tree
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:19:33.983608+00:00
-- url     : https://prove2.me/theorems/87ba8030-ecfb-471d-8660-afb190145a3b
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LU.Tree` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LU.Tree` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LU.Tree` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LU.Tree (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LU/Tree.lean)

import Definitions.Def_CK_CKLaneN4_LU_Check
import Definitions.Def_CK_CKLaneN4_LU_Origin

-- ===== source module CKLaneN4.LU.Tree =====
section
/-
Lane N4b — k-d tree cover of the `(a,t)` chart and its soundness.

Leaves: `cell c` (box must equal the node box; `cellCheck c = true` is supplied separately, one
kernel decision per cell) or `origin` (node box inside `[0,2^-9] × [0,2^-8]`, closed by the analytic
lemma `origin_nonneg`, since there `b = a + t(1/2 - a) ≤ 2^-8`).
-/

set_option autoImplicit false

namespace CKLaneN4.LU

open GeneralCK

inductive LTree where
  | cell (c : Cell)
  | origin
  | sa (m : ℕ) (l r : LTree)
  | st (m : ℕ) (l r : LTree)

def treeCheck : ℕ → ℕ → ℕ → ℕ → LTree → Bool
  | a0, a1, t0, t1, .cell c =>
      decide (c.a0 = a0) && decide (c.a1 = a1) && decide (c.t0 = t0) && decide (c.t1 = t1)
  | _, a1, _, t1, .origin => decide (a1 ≤ 2 ^ 55) && decide (t1 ≤ 2 ^ 56)
  | a0, a1, t0, t1, .sa m l r =>
      decide (a0 ≤ m) && decide (m ≤ a1) && treeCheck a0 m t0 t1 l && treeCheck m a1 t0 t1 r
  | a0, a1, t0, t1, .st m l r =>
      decide (t0 ≤ m) && decide (m ≤ t1) && treeCheck a0 a1 t0 m l && treeCheck a0 a1 m t1 r

def LTree.AllOk : LTree → Prop
  | .cell c => cellCheck c = true
  | .origin => True
  | .sa _ l r => l.AllOk ∧ r.AllOk
  | .st _ l r => l.AllOk ∧ r.AllOk

/-- The region statement on a chart box (coordinates at scale `2^64`). -/
def BoxGood (a0 a1 t0 t1 : ℕ) : Prop :=
  ∀ a t : ℝ, (a0 : ℝ) / 2 ^ 64 ≤ a → a ≤ (a1 : ℝ) / 2 ^ 64 → (t0 : ℝ) / 2 ^ 64 ≤ t →
    t ≤ (t1 : ℝ) / 2 ^ 64 → 0 < a → 0 < t → 0 ≤ Gexpr a (bAt a t)

theorem origin_box {a t : ℝ} (ha : a ≤ ((2 ^ 55 : ℕ) : ℝ) / 2 ^ 64)
    (ht : t ≤ ((2 ^ 56 : ℕ) : ℝ) / 2 ^ 64) (hapos : 0 < a) (htpos : 0 < t) :
    0 ≤ Gexpr a (bAt a t) := by
  have ha' : a ≤ 1 / 512 := by
    have e : ((2 ^ 55 : ℕ) : ℝ) / 2 ^ 64 = 1 / 512 := by norm_num
    linarith
  have ht' : t ≤ 1 / 256 := by
    have e : ((2 ^ 56 : ℕ) : ℝ) / 2 ^ 64 = 1 / 256 := by norm_num
    linarith
  apply origin_nonneg hapos
  · unfold bAt
    have : 0 < t * (1 / 2 - a) := mul_pos htpos (by linarith)
    linarith
  · unfold bAt
    have : t * (1 / 2 - a) ≤ t * (1 / 2) := mul_le_mul_of_nonneg_left (by linarith) htpos.le
    linarith

theorem treeCheck_sound : ∀ (T : LTree) (a0 a1 t0 t1 : ℕ),
    treeCheck a0 a1 t0 t1 T = true → T.AllOk → BoxGood a0 a1 t0 t1
  | .cell c, a0, a1, t0, t1, h, hok => by
      simp only [treeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
      intro a t ha0 ha1 ht0 ht1 hapos _
      rw [← h0] at ha0
      rw [← h1] at ha1
      rw [← h2] at ht0
      rw [← h3] at ht1
      exact cellCheck_sound (cl := c) hok ha0 ha1 ht0 ht1 hapos
  | .origin, a0, a1, t0, t1, h, _ => by
      simp only [treeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h1, h2⟩ := h
      intro a t _ ha1 _ ht1 hapos htpos
      have hp : (0 : ℝ) < 2 ^ 64 := by positivity
      have e1 : (a1 : ℝ) / 2 ^ 64 ≤ ((2 ^ 55 : ℕ) : ℝ) / 2 ^ 64 :=
        div_le_div_of_nonneg_right (by exact_mod_cast h1) hp.le
      have e2 : (t1 : ℝ) / 2 ^ 64 ≤ ((2 ^ 56 : ℕ) : ℝ) / 2 ^ 64 :=
        div_le_div_of_nonneg_right (by exact_mod_cast h2) hp.le
      exact origin_box (ha1.trans e1) (ht1.trans e2) hapos htpos
  | .sa m l r, a0, a1, t0, t1, h, hok => by
      simp only [treeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨_, _⟩, hl⟩, hr⟩ := h
      have IHl := treeCheck_sound l a0 m t0 t1 hl hok.1
      have IHr := treeCheck_sound r m a1 t0 t1 hr hok.2
      intro a t ha0 ha1 ht0 ht1 hapos htpos
      rcases le_total a ((m : ℝ) / 2 ^ 64) with hm | hm
      · exact IHl a t ha0 hm ht0 ht1 hapos htpos
      · exact IHr a t hm ha1 ht0 ht1 hapos htpos
  | .st m l r, a0, a1, t0, t1, h, hok => by
      simp only [treeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨_, _⟩, hl⟩, hr⟩ := h
      have IHl := treeCheck_sound l a0 a1 t0 m hl hok.1
      have IHr := treeCheck_sound r a0 a1 m t1 hr hok.2
      intro a t ha0 ha1 ht0 ht1 hapos htpos
      rcases le_total t ((m : ℝ) / 2 ^ 64) with hm | hm
      · exact IHl a t ha0 ha1 ht0 hm hapos htpos
      · exact IHr a t ha0 ha1 hm ht1 hapos htpos

/-- Gluing two boxes along an `a`-split. -/
theorem boxGood_sa {a0 m a1 t0 t1 : ℕ} (hl : BoxGood a0 m t0 t1) (hr : BoxGood m a1 t0 t1) :
    BoxGood a0 a1 t0 t1 := by
  intro a t ha0 ha1 ht0 ht1 hapos htpos
  rcases le_total a ((m : ℝ) / 2 ^ 64) with hm | hm
  · exact hl a t ha0 hm ht0 ht1 hapos htpos
  · exact hr a t hm ha1 ht0 ht1 hapos htpos

/-- Gluing two boxes along a `t`-split. -/
theorem boxGood_st {a0 a1 t0 m t1 : ℕ} (hl : BoxGood a0 a1 t0 m) (hr : BoxGood a0 a1 m t1) :
    BoxGood a0 a1 t0 t1 := by
  intro a t ha0 ha1 ht0 ht1 hapos htpos
  rcases le_total t ((m : ℝ) / 2 ^ 64) with hm | hm
  · exact hl a t ha0 ha1 ht0 hm hapos htpos
  · exact hr a t ha0 ha1 hm ht1 hapos htpos

end CKLaneN4.LU

end


