-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_TMISound1
-- name    : CK_CKLaneM07_CE_TMISound1
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:46:14.223523+00:00
-- url     : https://prove2.me/theorems/493a7e66-6051-4d3d-ae13-c69db56618ed
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.TMISound1` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.TMISound1` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.TMISound1` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.TMISound1 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/TMISound1.lean)

import Definitions.Def_CK_CKLaneM07_CE_TMI
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

-- ===== source module CKLaneM07.CE.TMISound1 =====
section

/-!
# Lane M07 / CE-stat: soundness of the fixed-point Taylor-model kernel (part 1: polynomials, add, mulC)

Semantics: `rowEval y r = ∑ r_j y^j`, `pEval x y p = ∑ x^i rowEval y p_i` (Horner), and a Taylor model
`t` encloses `v` at `(x, y)` when `|v - pEval x y t.p / 2^PB| ≤ t.r / 2^PB` (`EnclAt`), for `|x|, |y| ≤ 1`.
-/

set_option autoImplicit false

namespace CKLaneM07.CE

noncomputable def rowEval (y : ℝ) : RowI → ℝ
  | [] => 0
  | a :: r => (a : ℝ) + y * rowEval y r

noncomputable def pEval (x y : ℝ) : PolI → ℝ
  | [] => 0
  | r :: p => rowEval y r + x * pEval x y p

/-- the fixed-point scale `2^PB` as a real -/
noncomputable def SC : ℝ := ((ONE : ℤ) : ℝ)

theorem SC_pos : 0 < SC := by
  unfold SC ONE; positivity

theorem SC_eq_nat : SC = ((ONEn : ℕ) : ℝ) := by
  unfold SC ONE ONEn; push_cast; ring

def EnclAt (x y v : ℝ) (t : TMI) : Prop :=
  |v - pEval x y t.p / SC| ≤ (t.r : ℝ) / SC

/-! ## Evaluation lemmas -/

theorem rowEval_rowAdd (y : ℝ) : ∀ p q : RowI, rowEval y (rowAdd p q) = rowEval y p + rowEval y q
  | [], q => by simp [rowAdd, rowEval]
  | a :: p, [] => by simp [rowAdd, rowEval]
  | a :: p, b :: q => by
      simp only [rowAdd, rowEval, rowEval_rowAdd y p q]
      push_cast; ring

theorem pEval_pAdd (x y : ℝ) : ∀ p q : PolI, pEval x y (pAdd p q) = pEval x y p + pEval x y q
  | [], q => by simp [pAdd, pEval]
  | a :: p, [] => by simp [pAdd, pEval]
  | a :: p, b :: q => by
      simp only [pAdd, pEval, pEval_pAdd x y p q, rowEval_rowAdd]
      ring

theorem rowEval_neg (y : ℝ) : ∀ r : RowI, rowEval y (r.map (fun a => -a)) = -rowEval y r
  | [] => by simp [rowEval]
  | a :: r => by
      simp only [List.map_cons, rowEval, rowEval_neg y r]
      push_cast; ring

theorem pEval_pNeg (x y : ℝ) : ∀ p : PolI, pEval x y (pNeg p) = -pEval x y p
  | [] => by simp [pNeg, pEval]
  | r :: p => by
      have := pEval_pNeg x y p
      simp only [pNeg, List.map_cons, pEval] at this ⊢
      rw [rowEval_neg, this]; ring

theorem natAbs_cast (a : ℤ) : ((a.natAbs : ℕ) : ℝ) = |(a : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem abs_rowEval_le {y : ℝ} (hy : |y| ≤ 1) : ∀ r : RowI, |rowEval y r| ≤ (rowAbs r : ℝ)
  | [] => by simp [rowEval, rowAbs]
  | a :: r => by
      have ih := abs_rowEval_le hy r
      have e : ((rowAbs (a :: r) : ℕ) : ℝ) = |(a : ℝ)| + (rowAbs r : ℝ) := by
        simp only [rowAbs, List.foldr_cons]; push_cast; rw [natAbs_cast]
      rw [e]
      simp only [rowEval]
      calc |(a : ℝ) + y * rowEval y r| ≤ |(a : ℝ)| + |y * rowEval y r| := abs_add_le _ _
        _ = |(a : ℝ)| + |y| * |rowEval y r| := by rw [abs_mul]
        _ ≤ |(a : ℝ)| + 1 * (rowAbs r : ℝ) := by
            gcongr
        _ = |(a : ℝ)| + (rowAbs r : ℝ) := by ring

theorem abs_pEval_le {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : ∀ p : PolI, |pEval x y p| ≤ (pAbs p : ℝ)
  | [] => by simp [pEval, pAbs]
  | r :: p => by
      have ih := abs_pEval_le hx hy p
      have e : ((pAbs (r :: p) : ℕ) : ℝ) = (rowAbs r : ℝ) + (pAbs p : ℝ) := by
        simp only [pAbs, List.foldr_cons]; push_cast; rfl
      rw [e]
      simp only [pEval]
      calc |rowEval y r + x * pEval x y p| ≤ |rowEval y r| + |x * pEval x y p| := abs_add_le _ _
        _ = |rowEval y r| + |x| * |pEval x y p| := by rw [abs_mul]
        _ ≤ (rowAbs r : ℝ) + 1 * (pAbs p : ℝ) := by
            gcongr
            exact abs_rowEval_le hy r
        _ = (rowAbs r : ℝ) + (pAbs p : ℝ) := by ring

/-! ## Sums, negation -/

theorem EnclAt.add {x y u v : ℝ} {s t : TMI} (hs : EnclAt x y u s) (ht : EnclAt x y v t) :
    EnclAt x y (u + v) (s.add t) := by
  unfold EnclAt at *
  simp only [TMI.add, pEval_pAdd]
  have hS := SC_pos
  push_cast
  rw [add_div, add_div]
  calc |u + v - (pEval x y s.p / SC + pEval x y t.p / SC)|
      = |(u - pEval x y s.p / SC) + (v - pEval x y t.p / SC)| := by ring_nf
    _ ≤ |u - pEval x y s.p / SC| + |v - pEval x y t.p / SC| := abs_add_le _ _
    _ ≤ (s.r : ℝ) / SC + (t.r : ℝ) / SC := add_le_add hs ht

theorem EnclAt.neg {x y u : ℝ} {s : TMI} (hs : EnclAt x y u s) : EnclAt x y (-u) s.neg := by
  unfold EnclAt at *
  simp only [TMI.neg, pEval_pNeg]
  calc |-u - -pEval x y s.p / SC| = |u - pEval x y s.p / SC| := by
        rw [← abs_neg]; ring_nf
    _ ≤ (s.r : ℝ) / SC := hs

theorem EnclAt.sub {x y u v : ℝ} {s t : TMI} (hs : EnclAt x y u s) (ht : EnclAt x y v t) :
    EnclAt x y (u - v) (s.sub t) := by
  have := hs.add ht.neg
  simpa [TMI.sub, sub_eq_add_neg] using this

theorem EnclAt.const (x y : ℝ) (c : ℤ) : EnclAt x y ((c : ℝ) / SC) (TMI.const c) := by
  unfold EnclAt TMI.const
  simp [pEval, rowEval]

theorem EnclAt.addC {x y u : ℝ} {s : TMI} (c : ℤ) (hs : EnclAt x y u s) :
    EnclAt x y (u + (c : ℝ) / SC) (s.addC c) := by
  have := hs.add (EnclAt.const x y c)
  simpa [TMI.addC] using this

theorem EnclAt.weaken {x y u : ℝ} {s : TMI} {r' : ℕ} (hs : EnclAt x y u s) (hr : s.r ≤ r') :
    EnclAt x y u ⟨s.p, r'⟩ := by
  unfold EnclAt at *
  have hS := SC_pos
  calc |u - pEval x y s.p / SC| ≤ (s.r : ℝ) / SC := hs
    _ ≤ (r' : ℝ) / SC := by gcongr

theorem EnclAt.congr {x y u u' : ℝ} {s : TMI} (hs : EnclAt x y u s) (h : u = u') : EnclAt x y u' s :=
  h ▸ hs

end CKLaneM07.CE

end


