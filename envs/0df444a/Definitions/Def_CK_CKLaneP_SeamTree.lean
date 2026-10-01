-- Prove2me | Definitions.Def_CK_CKLaneP_SeamTree
-- name    : CK_CKLaneP_SeamTree
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T11:47:52.00548+00:00
-- url     : https://prove2.me/theorems/c98b2353-1ac7-45b1-bcee-70e1e398d66f
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamTree` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamTree` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamTree` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamTree (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamTree.lean)

import Definitions.Def_CK_CKLaneP_SeamNCheckB
import Definitions.Def_CK_CKLaneP_SeamWCheck
import Definitions.Def_CK_CKLaneP_SeamWKCheck
import Definitions.Def_CK_CKLaneP_SeamWBCheck
import Definitions.Def_CK_CKLaneP_SeamVCheck

-- ===== source module CKLaneP.SeamTree =====
section
/-
Lane P — the seam cover tree: a binary split tree over `(p, t)` boxes whose leaves are the
certified cell checkers (N-A, N-B, W-A, W-K, W-B, V) or a dispatch `tq` to the small-scale lemma (`q ≤ qT`).

* `SeamAt p q`      : every stationary seam point at `(p, q)` has `seamCurve ≥ 0`.
* `SeamBox p0 p1 t0 t1` : `SeamAt` on the closed box `p ∈ [p0,p1]`, `(q−p) ∈ [t0,t1]·(S/2−p)`.
* `STree.check_sound`   : a checked tree gives `SeamBox` of its root box.
* `SeamBox.splitP/splitT` : gluing of boxes proved in different modules.
Everything is conditional on the double-cap owner (`hdouble`, used for `DC ≥ 0`) and on the
small-scale lemma `hT`.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

/-- The seam conclusion at `(p, q)`. -/
def SeamAt (p q : ℝ) : Prop :=
  ∀ ys : ℝ, 0 < ys → 2 * q - 1 / 10000 < ys → ys < 1 / 10000 - 2 * p →
    seamD (1 / 10000) (H p) (H q) ys = 0 → 0 ≤ seamCurve (1 / 10000) (H p) (H q) ys

/-- The seam conclusion on a closed `(p, t)` box. -/
def SeamBox (p0 p1 t0 t1 : ℚ) : Prop :=
  ∀ p q : ℝ, 0 < p → p < q → ((p0 : ℚ) : ℝ) ≤ p → p ≤ ((p1 : ℚ) : ℝ) →
    ((t0 : ℚ) : ℝ) * (1 / 10000 / 2 - p) ≤ q - p → q - p ≤ ((t1 : ℚ) : ℝ) * (1 / 10000 / 2 - p) →
    SeamAt p q

theorem SeamBox.splitP {p0 m p1 t0 t1 : ℚ} (ha : SeamBox p0 m t0 t1) (hb : SeamBox m p1 t0 t1) :
    SeamBox p0 p1 t0 t1 := by
  intro p q hp hpq hp0 hp1 ht0 ht1
  rcases le_total p ((m : ℚ) : ℝ) with h | h
  · exact ha p q hp hpq hp0 h ht0 ht1
  · exact hb p q hp hpq h hp1 ht0 ht1

theorem SeamBox.splitT {p0 p1 t0 m t1 : ℚ} (ha : SeamBox p0 p1 t0 m) (hb : SeamBox p0 p1 m t1) :
    SeamBox p0 p1 t0 t1 := by
  intro p q hp hpq hp0 hp1 ht0 ht1
  rcases le_total (q - p) (((m : ℚ) : ℝ) * (1 / 10000 / 2 - p)) with h | h
  · exact ha p q hp hpq hp0 hp1 ht0 h
  · exact hb p q hp hpq hp0 hp1 h ht1

/-- Leaf witnesses (the box is supplied by the tree). -/
inductive SLeaf where
  | nA (np0 np1 nq nvb nva : ℕ) (xb : ℚ) (nxb nx2 : ℕ)
  | nB (np0 np1 nq nvb nva : ℕ) (xb : ℚ) (nxb nx2 : ℕ)
  | wA (np0 np1 nql nq nvb nva : ℕ) (xb : ℚ) (nxb nx2 : ℕ)
  | wK (np0 np1 nql nq nvb nva : ℕ) (xb : ℚ) (nxb nx2 : ℕ) (xK : ℚ) (nxK nvK nvH : ℕ)
  | wB (np0 np1 nql nq nvb nva : ℕ) (xb : ℚ) (nxb nx2 : ℕ)
  | v (np0 np1 nql nq nvb nva nxv : ℕ)
  | tq

/-- Binary split trees over `(p, t)` boxes. -/
inductive STree where
  | leaf (l : SLeaf)
  | sp (m : ℚ) (a b : STree)
  | st (m : ℚ) (a b : STree)

/-- Leaf check on the box `[p0,p1] × [t0,t1]`. -/
def SLeaf.check (qT p0 p1 t0 t1 : ℚ) : SLeaf → Bool
  | .nA np0 np1 nq nvb nva xb nxb nx2 =>
      ncheckA ⟨p0, p1, np0, np1, t0, t1, nq, nvb, nva, xb, nxb, nx2⟩
  | .nB np0 np1 nq nvb nva xb nxb nx2 =>
      ncheckB ⟨p0, p1, np0, np1, t0, t1, nq, nvb, nva, xb, nxb, nx2⟩
  | .wA np0 np1 nql nq nvb nva xb nxb nx2 =>
      wcheckA ⟨p0, p1, np0, np1, t0, t1, nql, nq, nvb, nva, xb, nxb, nx2⟩
  | .wK np0 np1 nql nq nvb nva xb nxb nx2 xK nxK nvK nvH =>
      wcheckK ⟨p0, p1, np0, np1, t0, t1, nql, nq, nvb, nva, xb, nxb, nx2⟩ xK nxK nvK nvH
  | .wB np0 np1 nql nq nvb nva xb nxb nx2 =>
      wcheckB ⟨p0, p1, np0, np1, t0, t1, nql, nq, nvb, nva, xb, nxb, nx2⟩
  | .v np0 np1 nql nq nvb nva nxv =>
      vcheck ⟨p0, p1, np0, np1, t0, t1, nql, nq, nvb, nva, nxv⟩
  | .tq => decide (0 ≤ t1 ∧ p1 + t1 * (Sq / 2 - p0) ≤ qT)

/-- Tree check on the box `[p0,p1] × [t0,t1]`. -/
def STree.check (qT : ℚ) : STree → ℚ → ℚ → ℚ → ℚ → Bool
  | .leaf l, p0, p1, t0, t1 => l.check qT p0 p1 t0 t1
  | .sp m a b, p0, p1, t0, t1 => a.check qT p0 m t0 t1 && b.check qT m p1 t0 t1
  | .st m a b, p0, p1, t0, t1 => a.check qT p0 p1 t0 m && b.check qT p0 p1 m t1

theorem SLeaf.check_sound (hdouble : CanonicalDoubleCapEntropyEndpoints) (qT : ℚ)
    (hT : ∀ p q : ℝ, 0 < p → p < q → q ≤ ((qT : ℚ) : ℝ) → SeamAt p q)
    (l : SLeaf) (p0 p1 t0 t1 : ℚ) (h : l.check qT p0 p1 t0 t1 = true) :
    SeamBox p0 p1 t0 t1 := by
  intro p q hp hpq hp0 hp1 ht0 ht1 ys hys0 hysq hysS hstat
  cases l with
  | nA np0 np1 nq nvb nva xb nxb nx2 =>
      exact ncheckA_sound hdouble _ h hp0 hp1 ht0 ht1 hpq hys0 hysS hstat
  | nB np0 np1 nq nvb nva xb nxb nx2 =>
      exact ncheckB_sound hdouble _ h hp0 hp1 ht0 ht1 hysq hysS hstat
  | wA np0 np1 nql nq nvb nva xb nxb nx2 =>
      exact wcheckA_sound hdouble _ h hp0 hp1 ht0 ht1 hys0 hysS hstat
  | wK np0 np1 nql nq nvb nva xb nxb nx2 xK nxK nvK nvH =>
      exact wcheckK_sound hdouble _ xK nxK nvK nvH h hp0 hp1 ht0 ht1 hys0 hysS hstat
  | wB np0 np1 nql nq nvb nva xb nxb nx2 =>
      exact wcheckB_sound hdouble _ h hp0 hp1 ht0 ht1 hysq hysS hstat
  | v np0 np1 nql nq nvb nva nxv =>
      exact (vcheck_sound _ h hp hpq hp0 hp1 ht0 ht1 hys0 hysS hstat).elim
  | tq =>
      simp only [SLeaf.check, decide_eq_true_eq] at h
      obtain ⟨ht1nn, hq⟩ := h
      have ht1R : (0 : ℝ) ≤ ((t1 : ℚ) : ℝ) := by exact_mod_cast ht1nn
      have hqR : ((p1 : ℚ) : ℝ) + ((t1 : ℚ) : ℝ) * (1 / 10000 / 2 - ((p0 : ℚ) : ℝ)) ≤
          ((qT : ℚ) : ℝ) := by
        have := (Rat.cast_le (K := ℝ)).mpr hq
        push_cast at this
        rw [Sq_cast] at this
        exact this
      have h1 : ((t1 : ℚ) : ℝ) * (1 / 10000 / 2 - p) ≤
          ((t1 : ℚ) : ℝ) * (1 / 10000 / 2 - ((p0 : ℚ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) ht1R
      exact hT p q hp hpq (by linarith) ys hys0 hysq hysS hstat

theorem STree.check_sound (hdouble : CanonicalDoubleCapEntropyEndpoints) (qT : ℚ)
    (hT : ∀ p q : ℝ, 0 < p → p < q → q ≤ ((qT : ℚ) : ℝ) → SeamAt p q) :
    ∀ (T : STree) (p0 p1 t0 t1 : ℚ), T.check qT p0 p1 t0 t1 = true → SeamBox p0 p1 t0 t1 := by
  intro T
  induction T with
  | leaf l =>
      intro p0 p1 t0 t1 h
      exact SLeaf.check_sound hdouble qT hT l p0 p1 t0 t1 h
  | sp m a b iha ihb =>
      intro p0 p1 t0 t1 h
      simp only [STree.check, Bool.and_eq_true] at h
      exact SeamBox.splitP (iha _ _ _ _ h.1) (ihb _ _ _ _ h.2)
  | st m a b iha ihb =>
      intro p0 p1 t0 t1 h
      simp only [STree.check, Bool.and_eq_true] at h
      exact SeamBox.splitT (iha _ _ _ _ h.1) (ihb _ _ _ _ h.2)

end CKLaneP

end


