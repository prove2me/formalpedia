-- Prove2me | Definitions.Def_QMCLeafB_volkill
-- name    : QMCLeafB_volkill
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T09:13:38.252558+00:00
-- url     : https://prove2.me/theorems/4c8ebfcb-4431-44d8-93e0-5d35a5ac6950
-- title:
--   QMCLeafB volkill
-- statement:
--   # `Check_volkill_m3` — the volume obstruction at the sliver, part 1
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_parts_m2
/-
# `Check_volkill_m3` — the volume obstruction at the sliver, part 1

* §1 `anyOk` splitting: an all-`false` verdict forces every round below the horizon to be a cut;
* §2 **a Euclidean ball inside an ellipsoid caps the shape determinant**: if the ellipsoid
  `{z | (z − c) ⬝ᵥ (A *ᵥ (z − c)) ≤ 1}` contains the ball of radius `r > 0` around `z₀`, then
  `det A ≤ 384 / r^8` in dimension `4`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QMCLeafB.VolKillM3

/-! ## 1.  The verdict bit splits the run -/

theorem ok_false_of_anyOk_false (ok : ℕ → Bool) :
    ∀ T k, k < T → QMCLeafB.SimLoop.anyOk ok T = false → ok k = false
  | 0, k, hk, _ => absurd hk (Nat.not_lt_zero k)
  | (T + 1), k, hk, h => by
      rw [QMCLeafB.SimLoop.anyOk_succ] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact ok_false_of_anyOk_false ok T k hlt (by
          rcases Bool.or_eq_false_iff.mp h with ⟨_, h2⟩; exact h2)
      · rcases Bool.or_eq_false_iff.mp h with ⟨h1, _⟩; exact h1

theorem anyOk_true_of_ok (ok : ℕ → Bool) :
    ∀ T k, k < T → ok k = true → QMCLeafB.SimLoop.anyOk ok T = true
  | 0, k, hk, _ => absurd hk (Nat.not_lt_zero k)
  | (T + 1), k, hk, h => by
      rw [QMCLeafB.SimLoop.anyOk_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact Bool.or_eq_true_iff.mpr (Or.inr (anyOk_true_of_ok ok T k hlt h))
      · exact Bool.or_eq_true_iff.mpr (Or.inl h)

#print axioms QMCLeafB.VolKillM3.ok_false_of_anyOk_false
#print axioms QMCLeafB.VolKillM3.anyOk_true_of_ok

/-! ## 2.  A contained ball caps the determinant -/

theorem mulVec_single (A : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) :
    A *ᵥ (Pi.single i (1 : ℝ)) = fun k => A k i := by
  ext k
  simp [Matrix.mulVec, Pi.single_apply]

theorem single_dot_single (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (Pi.single i (1 : ℝ) : Fin 4 → ℝ) ⬝ᵥ (A *ᵥ Pi.single j (1 : ℝ)) = A i j := by
  rw [mulVec_single]
  simp [dotProduct, Pi.single_apply]

theorem dot_single_self (i : Fin 4) :
    (Pi.single i (1 : ℝ) : Fin 4 → ℝ) ⬝ᵥ (Pi.single i (1 : ℝ) : Fin 4 → ℝ) = 1 := by
  simp [dotProduct, Pi.single_apply]

theorem dot_single_ne {i j : Fin 4} (h : i ≠ j) :
    (Pi.single i (1 : ℝ) : Fin 4 → ℝ) ⬝ᵥ (Pi.single j (1 : ℝ) : Fin 4 → ℝ) = 0 := by
  simp [dotProduct, Pi.single_apply, h, Ne.symm h]

theorem smul_dot_smul' (x y : ℝ) (u v : Fin 4 → ℝ) :
    (x • u) ⬝ᵥ (y • v) = (x * y) * (u ⬝ᵥ v) := by
  rw [dotProduct_smul, smul_dotProduct]
  ring

#print axioms QMCLeafB.VolKillM3.smul_dot_smul'

theorem quad_smul (A : Matrix (Fin 4) (Fin 4) ℝ) (x y : ℝ) (u v : Fin 4 → ℝ) :
    (x • u) ⬝ᵥ (A *ᵥ (y • v)) = (x * y) * (u ⬝ᵥ (A *ᵥ v)) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  ring

theorem quad_pair (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    ((Pi.single i (1 : ℝ) : Fin 4 → ℝ) + (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) ⬝ᵥ
      (A *ᵥ ((Pi.single i (1 : ℝ) : Fin 4 → ℝ) + (Pi.single j (1 : ℝ) : Fin 4 → ℝ)))
      = A i i + A i j + A j i + A j j := by
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, single_dot_single]
  ring

theorem pair_norm {i j : Fin 4} (h : i ≠ j) :
    ((Pi.single i (1 : ℝ) : Fin 4 → ℝ) + (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) ⬝ᵥ
      ((Pi.single i (1 : ℝ) : Fin 4 → ℝ) + (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) = 2 := by
  simp only [add_dotProduct, dotProduct_add, dot_single_self, dot_single_ne h,
    dot_single_ne (Ne.symm h)]
  norm_num

theorem quad_pair_sub (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    ((Pi.single i (1 : ℝ) : Fin 4 → ℝ) - (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) ⬝ᵥ
      (A *ᵥ ((Pi.single i (1 : ℝ) : Fin 4 → ℝ) - (Pi.single j (1 : ℝ) : Fin 4 → ℝ)))
      = A i i - A i j - A j i + A j j := by
  simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add,
    single_dot_single]
  ring

theorem pair_norm_sub {i j : Fin 4} (h : i ≠ j) :
    ((Pi.single i (1 : ℝ) : Fin 4 → ℝ) - (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) ⬝ᵥ
      ((Pi.single i (1 : ℝ) : Fin 4 → ℝ) - (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) = 2 := by
  simp only [sub_dotProduct, dotProduct_sub, dot_single_self, dot_single_ne h,
    dot_single_ne (Ne.symm h)]
  norm_num

#print axioms QMCLeafB.VolKillM3.pair_norm
#print axioms QMCLeafB.VolKillM3.quad_pair_sub
#print axioms QMCLeafB.VolKillM3.pair_norm_sub

theorem quad_small {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : A.PosDef)
    {c z₀ : Fin 4 → ℝ} {r : ℝ}
    (hsub : ∀ z : Fin 4 → ℝ, (z - z₀) ⬝ᵥ (z - z₀) ≤ r ^ 2 →
      (z - c) ⬝ᵥ (A *ᵥ (z - c)) ≤ 1) :
    ∀ w : Fin 4 → ℝ, w ⬝ᵥ w ≤ r ^ 2 → w ⬝ᵥ (A *ᵥ w) ≤ 1 := by
  have hq0 : 0 ≤ (z₀ - c) ⬝ᵥ (A *ᵥ (z₀ - c)) := hA.posSemidef.dotProduct_mulVec_nonneg _
  intro w hw
  have hp : (z₀ + w - c) ⬝ᵥ (A *ᵥ (z₀ + w - c)) ≤ 1 := by
    refine hsub (z₀ + w) ?_
    have h : z₀ + w - z₀ = w := by abel
    rw [h]; exact hw
  have hm : (z₀ - w - c) ⬝ᵥ (A *ᵥ (z₀ - w - c)) ≤ 1 := by
    refine hsub (z₀ - w) ?_
    have h : z₀ - w - z₀ = -w := by abel
    rw [h]
    have h2 : (-w) ⬝ᵥ (-w) = w ⬝ᵥ w := by simp
    rw [h2]; exact hw
  have key : (z₀ + w - c) ⬝ᵥ (A *ᵥ (z₀ + w - c))
      + (z₀ - w - c) ⬝ᵥ (A *ᵥ (z₀ - w - c))
      = 2 * ((z₀ - c) ⬝ᵥ (A *ᵥ (z₀ - c))) + 2 * (w ⬝ᵥ (A *ᵥ w)) := by
    have e1 : z₀ + w - c = (z₀ - c) + w := by abel
    have e2 : z₀ - w - c = (z₀ - c) - w := by abel
    simp only [e1, e2, Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
      dotProduct_add, dotProduct_sub]
    ring
  linarith

#print axioms QMCLeafB.VolKillM3.quad_small

theorem det_le_of_ball_subset {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : A.PosDef)
    {c z₀ : Fin 4 → ℝ} {r : ℝ} (hr : 0 < r)
    (hsub : ∀ z : Fin 4 → ℝ, (z - z₀) ⬝ᵥ (z - z₀) ≤ r ^ 2 →
      (z - c) ⬝ᵥ (A *ᵥ (z - c)) ≤ 1) :
    A.det ≤ 384 * (1 / r) ^ 8 := by
  have hsmall := quad_small hA hsub
  have hcomm : ∀ i j : Fin 4, A i j = A j i := by
    intro i j
    have h := congr_fun (congr_fun hA.isHermitian i) j
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hdiag : ∀ i : Fin 4, A i i ≤ 1 / r ^ 2 := by
    intro i
    have hnorm : (r • (Pi.single i (1 : ℝ) : Fin 4 → ℝ)) ⬝ᵥ
        (r • (Pi.single i (1 : ℝ) : Fin 4 → ℝ)) ≤ r ^ 2 := by
      rw [smul_dot_smul', dot_single_self]
      nlinarith
    have h := hsmall _ hnorm
    rw [quad_smul, single_dot_single] at h
    rw [le_div_iff₀ hr2]
    nlinarith
  have hnn : ∀ i : Fin 4, 0 ≤ A i i := by
    intro i
    have h' := hA.posSemidef.dotProduct_mulVec_nonneg (Pi.single i (1 : ℝ) : Fin 4 → ℝ)
    rw [show star (Pi.single i (1 : ℝ) : Fin 4 → ℝ) = (Pi.single i (1 : ℝ) : Fin 4 → ℝ)
      by simp, single_dot_single] at h'
    exact h'
  have hoff : ∀ i j : Fin 4, A i j ≤ 2 / r ^ 2 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have h1 := hdiag i
      have hmul : A i i * r ^ 2 ≤ 1 := by
        have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hr2)
        calc A i i * r ^ 2 ≤ (1 / r ^ 2) * r ^ 2 := h2
          _ = 1 := by field_simp
      rw [le_div_iff₀ hr2]
      linarith
    · have hnorm : ((r / 2) • ((Pi.single i (1 : ℝ) : Fin 4 → ℝ)
          + (Pi.single j (1 : ℝ) : Fin 4 → ℝ))) ⬝ᵥ
          ((r / 2) • ((Pi.single i (1 : ℝ) : Fin 4 → ℝ)
          + (Pi.single j (1 : ℝ) : Fin 4 → ℝ))) ≤ r ^ 2 := by
        rw [smul_dot_smul', pair_norm hij]
        nlinarith
      have h := hsmall _ hnorm
      rw [quad_smul, quad_pair, hcomm j i] at h
      have hd : 0 ≤ A i i + A j j := by linarith [hnn i, hnn j]
      have hr24 : (0 : ℝ) ≤ r ^ 2 / 4 := by positivity
      rw [le_div_iff₀ hr2]
      nlinarith [h, hd, hr24]
  have hoff2 : ∀ i j : Fin 4, -(2 / r ^ 2) ≤ A i j := by
    intro i j
    rw [show -(2 / r ^ 2) = (-2) / r ^ 2 by ring]
    rw [div_le_iff₀ hr2]
    by_cases hij : i = j
    · subst hij
      have h1 := hnn i
      nlinarith [h1, hr2]
    · have hnorm : ((r / 2) • ((Pi.single i (1 : ℝ) : Fin 4 → ℝ)
          - (Pi.single j (1 : ℝ) : Fin 4 → ℝ))) ⬝ᵥ
          ((r / 2) • ((Pi.single i (1 : ℝ) : Fin 4 → ℝ)
          - (Pi.single j (1 : ℝ) : Fin 4 → ℝ))) ≤ r ^ 2 := by
        rw [smul_dot_smul', pair_norm_sub hij]
        nlinarith
      have h := hsmall _ hnorm
      rw [quad_smul, quad_pair_sub, hcomm j i] at h
      have hd : 0 ≤ A i i + A j j := by linarith [hnn i, hnn j]
      have hr24 : (0 : ℝ) ≤ r ^ 2 / 4 := by positivity
      nlinarith [h, hd, hr24]
  have hentry : ∀ i j : Fin 4, |A i j| ≤ 2 / r ^ 2 := by
    intro i j
    rw [abs_le]
    exact ⟨hoff2 i j, hoff i j⟩
  have hdet : |A.det| ≤ 24 * (2 / r ^ 2) ^ 4 := by
    have h := Matrix.det_le (A := A) (abv := AbsoluteValue.abs) (x := 2 / r ^ 2) hentry
    have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num
    simpa [hfac] using h
  have h1 : A.det ≤ |A.det| := le_abs_self _
  have heq : 24 * (2 / r ^ 2) ^ 4 = 384 * (1 / r) ^ 8 := by
    field_simp
    ring
  linarith [h1, hdet, heq.le]

#print axioms QMCLeafB.VolKillM3.det_le_of_ball_subset

end QMCLeafB.VolKillM3


