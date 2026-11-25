-- Prove2me | solution 1 for Arxiv2003_13288.qca_differential_scattering
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:46:32.285052+00:00
-- url     : https://prove2.me/submissions/cc988cb9-6f39-402c-9b25-4ee5e842dcaf

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


lemma qd_ft_radial (h2 : ℝ → ℝ) (q q' : E3) (hq : ‖q‖ = ‖q'‖) :
    pairCorrFT h2 q' = pairCorrFT h2 q := by
  set R : E3 ≃ₗᵢ[ℝ] E3 := Submodule.reflection (ℝ ∙ (q - q'))ᗮ with hR
  have hRq : R q = q' := Submodule.reflection_sub hq
  unfold pairCorrFT
  rw [← hRq]
  have hmp := R.measurePreserving
  rw [← hmp.integral_comp R.toHomeomorph.measurableEmbedding]
  congr 1
  funext s
  rw [LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map]

lemma qd_norm (K θ : ℝ) (hK : 0 < K) (hθ : θ ∈ Set.Icc 0 Real.pi) (p u : E3)
    (hp : ‖p‖ ^ 2 = 1) (hu : ‖u‖ = 1) (hpu : inner ℝ p u = Real.cos θ) :
    ‖K • p - K • u‖ = ‖(2 * K * Real.sin (θ / 2)) • u‖ := by
  have hs : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [← smul_sub, norm_smul, norm_smul, hu, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hK, abs_of_nonneg (by positivity), mul_one]
  have h1 : ‖p - u‖ ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by
    rw [norm_sub_sq_real, hp, hu, hpu]
    have := Real.cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    have := Real.sin_sq_add_cos_sq (θ / 2)
    nlinarith
  have h2 : ‖p - u‖ = 2 * Real.sin (θ / 2) := by
    have := (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h1
    exact this
  rw [h2]; ring

theorem solution (n0 k K : ℝ) (hn0 : 0 < n0) (hk : 0 < k) (hK : 0 < K)
    (t0 : ℂ) (h2 : ℝ → ℝ) (hmeas : Measurable h2) (hint : IntegrableOn (fun r => r * h2 r) (Set.Ioi 0))
    (hint3 : Integrable (fun r : E3 => h2 ‖r‖)) (hg2 : ∀ r, -1 ≤ h2 r)
    (C : ℂ) (hC : C = qcaSelfEnergy n0 k t0 h2 / n0) (u e1 e2 : E3)
    (hframe : Orthonormal ℝ ![u, e1, e2]) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    diffScatPolar (qcaVertex n0 K C h2) u e1 e2 θ =
      n0 * ‖C‖ ^ 2 * (1 + Real.cos θ ^ 2) / (4 * Real.pi) *
        (1 + n0 * pairCorrFT h2 ((2 * K * Real.sin (θ / 2)) • u)) := by
  have hu : ‖u‖ = 1 := by simpa using hframe.1 0
  have h1 : ‖e1‖ = 1 := by simpa using hframe.1 1
  have h2' : ‖e2‖ = 1 := by simpa using hframe.1 2
  have hu1 : inner ℝ u e1 = 0 := by simpa using hframe.2 (show (0 : Fin 3) ≠ 1 by decide)
  have hu2 : inner ℝ u e2 = 0 := by simpa using hframe.2 (show (0 : Fin 3) ≠ 2 by decide)
  have h12 : inner ℝ e1 e2 = 0 := by simpa using hframe.2 (show (1 : Fin 3) ≠ 2 by decide)
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have h11 : inner ℝ e1 e1 = 1 := by rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have h22 : inner ℝ e2 e2 = 1 := by rw [real_inner_self_eq_norm_sq, h2']; norm_num
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
  obtain ⟨H, hH⟩ : ∃ H, H = pairCorrFT h2 ((2 * K * Real.sin (θ / 2)) • u) := ⟨_, rfl⟩
  rw [← hH]
  have hV : ∀ φ : ℝ, qcaVertex n0 K C h2 (scatDir u e1 e2 θ φ) u =
      ((n0 * ‖C‖ ^ 2 : ℝ) : ℂ) + ((n0 ^ 2 * ‖C‖ ^ 2 : ℝ) : ℂ) * H := by
    intro φ
    have e := qd_ft_radial h2 ((2 * K * Real.sin (θ / 2)) • u)
      (K • scatDir u e1 e2 θ φ - K • u) (qd_norm K θ hK hθ _ u (hpp φ) hu (hpu φ)).symm
    unfold qcaVertex
    rw [e, hH]
  have hint' : ∀ φ : ℝ, ((2 * Real.pi : ℂ) ^ 2)⁻¹ * qcaVertex n0 K C h2 (scatDir u e1 e2 θ φ) u *
      unpolTransverse (scatDir u e1 e2 θ φ) u =
      ((2 * Real.pi : ℂ) ^ 2)⁻¹ * (((n0 * ‖C‖ ^ 2 : ℝ) : ℂ) + ((n0 ^ 2 * ‖C‖ ^ 2 : ℝ) : ℂ) * H) *
        ((1 + (Real.cos θ : ℂ) ^ 2) / 2) := by
    intro φ
    rw [is_unpol, hpu, hpp, hu, hV]
    push_cast
    ring
  unfold diffScatPolar
  simp only [hint']
  rw [intervalIntegral.integral_const]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [sub_zero, Complex.real_smul]
  push_cast
  field_simp
  ring

