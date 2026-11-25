-- Prove2me | solution 1 for Arxiv2003_13288.isa_dipole_differential_scattering
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:44:43.453985+00:00
-- url     : https://prove2.me/submissions/27764214-7e4c-4e61-9f6e-c0f37a109f46

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology
open Arxiv2003_13288

lemma is_tr_dyad (v : E3) : Matrix.trace (dyad v) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Matrix.trace, dyad, Fin.sum_univ_three, sq]

lemma is_tr_dyad_mul (v w : E3) :
    Matrix.trace (dyad v * dyad w) = (((inner ℝ v w) ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dyad, Fin.sum_univ_three,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  ring

lemma is_unpol (v w : E3) :
    unpolTransverse v w = (1 / 2) * (3 - ((‖v‖ ^ 2 : ℝ) : ℂ) - ((‖w‖ ^ 2 : ℝ) : ℂ) +
      (((inner ℝ v w) ^ 2 : ℝ) : ℂ)) := by
  unfold unpolTransverse transProj
  have : (1 - dyad v) * (1 - dyad w) = 1 - dyad v - dyad w + dyad v * dyad w := by noncomm_ring
  rw [this, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_one,
    is_tr_dyad, is_tr_dyad, is_tr_dyad_mul]
  simp

theorem solution (n0 : ℝ) (hn0 : 0 < n0) (t0 : ℂ) (u e1 e2 : E3)
    (hframe : Orthonormal ℝ ![u, e1, e2]) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    diffScatPolar (isaDipoleVertex n0 t0) u e1 e2 θ =
      (1 + Real.cos θ ^ 2) / (4 * Real.pi) * n0 * ‖t0‖ ^ 2 := by
  have hu : ‖u‖ = 1 := by simpa using hframe.1 0
  have h1 : ‖e1‖ = 1 := by simpa using hframe.1 1
  have h2 : ‖e2‖ = 1 := by simpa using hframe.1 2
  have hu1 : inner ℝ u e1 = 0 := by simpa using hframe.2 (show (0 : Fin 3) ≠ 1 by decide)
  have hu2 : inner ℝ u e2 = 0 := by simpa using hframe.2 (show (0 : Fin 3) ≠ 2 by decide)
  have h12 : inner ℝ e1 e2 = 0 := by simpa using hframe.2 (show (1 : Fin 3) ≠ 2 by decide)
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have h11 : inner ℝ e1 e1 = 1 := by rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have h22 : inner ℝ e2 e2 = 1 := by rw [real_inner_self_eq_norm_sq, h2]; norm_num
  have hpu : ∀ φ : ℝ, inner ℝ (scatDir u e1 e2 θ φ) u = Real.cos θ := by
    intro φ
    simp only [scatDir, inner_add_left, inner_smul_left, real_inner_comm u e1, real_inner_comm u e2,
      hu1, hu2, huu, conj_trivial]
    ring
  have hpp : ∀ φ : ℝ, ‖scatDir u e1 e2 θ φ‖ ^ 2 = 1 := by
    intro φ
    rw [← real_inner_self_eq_norm_sq]
    simp only [scatDir, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      real_inner_comm u e1, real_inner_comm u e2, real_inner_comm e1 e2, hu1, hu2, h12, huu, h11, h22,
      conj_trivial]
    have := Real.cos_sq_add_sin_sq θ
    have := Real.cos_sq_add_sin_sq φ
    nlinarith [this]
  have hint : ∀ φ : ℝ, ((2 * Real.pi : ℂ) ^ 2)⁻¹ * isaDipoleVertex n0 t0 (scatDir u e1 e2 θ φ) u *
      unpolTransverse (scatDir u e1 e2 θ φ) u =
      ((2 * Real.pi : ℂ) ^ 2)⁻¹ * ((n0 * ‖t0‖ ^ 2 : ℝ) : ℂ) * ((1 + (Real.cos θ : ℂ) ^ 2) / 2) := by
    intro φ
    rw [is_unpol, hpu, hpp, hu]
    unfold isaDipoleVertex
    push_cast
    ring
  unfold diffScatPolar
  simp only [hint]
  rw [intervalIntegral.integral_const]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [sub_zero, Complex.real_smul]
  push_cast
  field_simp
  ring

