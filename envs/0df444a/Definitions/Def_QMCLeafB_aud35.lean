-- Prove2me | Definitions.Def_QMCLeafB_aud35
-- name    : QMCLeafB_aud35
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:53:54.354106+00:00
-- url     : https://prove2.me/theorems/68e65988-159d-453e-b750-4be5d7cd9ac4
-- title:
--   QMCLeafB aud35
-- statement:
--   The Check_aud35_m8 module of the QMCLeafB library.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thinrec34
import Definitions.Def_QMCLeafB_dreg
import Definitions.Def_QMCLeafB_alcut33

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Aud35M8

open QuantumMaxCutEnergy
open QMCLeafB.BallFloor

/-! ## 1.  The two-point (parallelogram) core -/

theorem qfR_le_four_of_segment {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hpsd : A.PosSemidef)
    {a c v : Fin N → ℝ}
    (hmem : ∀ t : ℝ, |t| ≤ 1 / 2 → (c + t • v - a) ⬝ᵥ (A *ᵥ (c + t • v - a)) ≤ 1) :
    qfR A v ≤ 4 := by
  have e1 : c + (1 / 2 : ℝ) • v - a = (1 / 2 : ℝ) • v + (c - a) := by abel
  have e2 : c + (-(1 / 2) : ℝ) • v - a = -((1 / 2 : ℝ) • v) + (c - a) := by
    rw [neg_smul]; abel
  have hplus : qfR A ((1 / 2 : ℝ) • v + (c - a)) ≤ 1 := by
    have h := hmem (1 / 2) (by norm_num)
    rw [e1] at h
    simpa only [qfR] using h
  have hminus : qfR A (-((1 / 2 : ℝ) • v) + (c - a)) ≤ 1 := by
    have h := hmem (-(1 / 2)) (by norm_num)
    rw [e2] at h
    simpa only [qfR] using h
  have hpar := qfR_add_vec_add_neg A ((1 / 2 : ℝ) • v) (c - a)
  have hnonneg : 0 ≤ qfR A (c - a) := by
    have h := hpsd.dotProduct_mulVec_nonneg (c - a)
    simpa [qfR, star_trivial] using h
  have hhalf : qfR A ((1 / 2 : ℝ) • v) ≤ 1 := by linarith
  have hsq : qfR A ((1 / 2 : ℝ) • v) = (1 / 4) * qfR A v := by
    rw [qfR_smul_vec]; norm_num
  rw [hsq] at hhalf
  linarith

#print axioms QMCLeafB.Aud35M8.qfR_le_four_of_segment

/-! ## 2.  The scaled quadratic-form bound for a parallelotope -/

theorem qfR_box_le {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hpsd : A.PosSemidef)
    {a c : Fin N → ℝ} (V : Matrix (Fin N) (Fin N) ℝ)
    (hbox : ∀ y : Fin N → ℝ, (∀ i, |y i| ≤ 1) →
      (c + V *ᵥ y - a) ⬝ᵥ (A *ᵥ (c + V *ᵥ y - a)) ≤ 1)
    (x : Fin N → ℝ) :
    qfR A (V *ᵥ x) ≤ 4 * ∑ i, x i ^ 2 := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp [qfR]
  have hS : 0 < ∑ i, x i ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      exact hx (funext (by simpa [not_exists] using h))
    refine Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, Finset.mem_univ i, ?_⟩
    rw [sq]; exact mul_self_pos.mpr hi
  set R : ℝ := Real.sqrt (∑ i, x i ^ 2) with hR
  have hRpos : 0 < R := Real.sqrt_pos.2 hS
  have hRsq : R ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hS.le
  have hcoord : ∀ i, |x i| ≤ R := by
    intro i
    have h1 : (x i) ^ 2 ≤ ∑ j, x j ^ 2 :=
      Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j))
        (Finset.mem_univ i)
    calc |x i| = Real.sqrt ((x i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ j, x j ^ 2) := Real.sqrt_le_sqrt h1
      _ = R := rfl
  have hseg : qfR A (R⁻¹ • (V *ᵥ x)) ≤ 4 := by
    refine qfR_le_four_of_segment hpsd (a := a) (c := c) (v := R⁻¹ • (V *ᵥ x)) ?_
    intro t ht
    have hy : ∀ i, |((t * R⁻¹) • x) i| ≤ 1 := by
      intro i
      have h1 : ((t * R⁻¹) • x) i = (t * R⁻¹) * x i := rfl
      rw [h1, abs_mul]
      have hRm : 0 ≤ R⁻¹ := le_of_lt (inv_pos.mpr hRpos)
      have hstep : |t| * R⁻¹ * |x i| ≤ ((1 / 2) * R⁻¹) * R := by
        refine mul_le_mul ?_ (hcoord i) (abs_nonneg _) (mul_nonneg (by norm_num) hRm)
        exact mul_le_mul_of_nonneg_right ht hRm
      have hone : ((1 / 2) * R⁻¹) * R = 1 / 2 := by
        rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hRpos)]; ring
      rw [abs_mul, abs_of_nonneg hRm] at *
      linarith
    have hm := hbox ((t * R⁻¹) • x) hy
    have hVe : V *ᵥ ((t * R⁻¹) • x) = t • (R⁻¹ • (V *ᵥ x)) := by
      rw [Matrix.mulVec_smul, smul_smul]
    rwa [hVe] at hm
  rw [qfR_smul_vec] at hseg
  have hRpos2 : 0 < (R⁻¹) ^ 2 := by positivity
  have hRs : (R⁻¹) ^ 2 * ∑ i, x i ^ 2 = 1 := by
    rw [← hRsq, inv_pow, inv_mul_cancel₀ (ne_of_gt (pow_pos hRpos 2))]
  nlinarith [hseg]

#print axioms QMCLeafB.Aud35M8.qfR_box_le

/-! ## 3.  The determinant ceiling: `det(V)² · det A ≤ 4ᴺ` -/

theorem qfR_transpose_mul {N : ℕ} (A V : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    qfR (Vᵀ * A * V) x = qfR A (V *ᵥ x) := by
  show x ⬝ᵥ ((Vᵀ * A * V) *ᵥ x) = (V *ᵥ x) ⬝ᵥ (A *ᵥ (V *ᵥ x))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
    dotProduct_comm]

#print axioms QMCLeafB.Aud35M8.qfR_transpose_mul

theorem det_sq_mul_det_le_four_pow {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {a c : Fin N → ℝ} (V : Matrix (Fin N) (Fin N) ℝ)
    (hbox : ∀ y : Fin N → ℝ, (∀ i, |y i| ≤ 1) →
      (c + V *ᵥ y - a) ⬝ᵥ (A *ᵥ (c + V *ᵥ y - a)) ≤ 1) :
    V.det ^ 2 * A.det ≤ 4 ^ N := by
  have hpsd : (Vᵀ * A * V).PosSemidef := by
    have h := hA.posSemidef.conjTranspose_mul_mul_same V
    have hc : (Vᴴ : Matrix (Fin N) (Fin N) ℝ) = Vᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rwa [hc] at h
  have hq : ∀ x : Fin N → ℝ, qfR ((1 / 4 : ℝ) • (Vᵀ * A * V)) x ≤ ∑ i, x i ^ 2 := by
    intro x
    rw [qfR_smul, qfR_transpose_mul]
    have := qfR_box_le hA.posSemidef (a := a) (c := c) V hbox x
    nlinarith
  have hdet : ((1 / 4 : ℝ) • (Vᵀ * A * V)).det ≤ 1 :=
    det_le_one_of_qf_le (hpsd.smul (by norm_num)) hq
  rw [Matrix.det_smul, Fintype.card_fin] at hdet
  have hdetB : (Vᵀ * A * V).det = V.det ^ 2 * A.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  rw [hdetB] at hdet
  have hmul : (1 / 4 : ℝ) ^ N * (4 : ℝ) ^ N = 1 := by
    rw [← mul_pow]; norm_num
  have hb : (0 : ℝ) < (4 : ℝ) ^ N := by positivity
  have hstep := mul_le_mul_of_nonneg_left hdet hb.le
  nlinarith [hstep, hmul, hb]

#print axioms QMCLeafB.Aud35M8.det_sq_mul_det_le_four_pow


/-! ## 4.  The engine-side criterion (statement; the assembly is the named residual)

Given §3 and the banked containment + halving budget, the criterion a body must SATISFY to admit an
all-false record is: every parallelotope it contains has content below `2^(n·n) · r^(n·n)`, with
`r = dq/(8(cAq+1))`.  The formal assembly is the residual of this file — see `aud35-m8.md`, §5, for
the exact term and the four ingredient lemmas (all banked/compiled here). -/

end QMCLeafB.Aud35M8


