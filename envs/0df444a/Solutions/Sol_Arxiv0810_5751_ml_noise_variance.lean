-- Prove2me | solution 1 for Arxiv0810_5751.ml_noise_variance
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:57:12.017399+00:00
-- url     : https://prove2.me/submissions/881ba5ab-d9b6-4bc6-90df-431ee6cbbfbc

import Mathlib
import Definitions.Def_Arxiv0810_5751_Basic

set_option autoImplicit false

open MeasureTheory Matrix
open scoped ComplexOrder
namespace Arxiv0810_5751

lemma ml_formula {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θ : Fin P → ℂ) (τ : ℝ) (hτ : 0 < τ) :
    whiteLogLik τ y s θ = -(M : ℝ) * Real.log Real.pi - M * Real.log τ - residSq y s θ / τ := by
  unfold whiteLogLik likelihood
  have hinv : ((τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ = ((τ : ℂ)⁻¹) • (1 : Matrix (Fin M) (Fin M) ℂ) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hτ.ne'), one_smul]
  have hdet : (((τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).det).re = τ ^ M := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← Complex.ofReal_pow,
      Complex.ofReal_re]
  have hq : (star (residual y s θ) ⬝ᵥ (((τ : ℂ)⁻¹) • (1 : Matrix (Fin M) (Fin M) ℂ)) *ᵥ
      residual y s θ).re = residSq y s θ / τ := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    unfold residSq
    simp only [dotProduct, Pi.star_apply, smul_eq_mul]
    rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum, div_eq_inv_mul]
    congr 1
    apply Finset.sum_congr rfl; intro m _
    rw [RCLike.star_def, mul_comm, Complex.mul_conj]
    simp
  rw [hinv, hdet, hq]
  have hpi : 0 < Real.pi ^ M := by positivity
  have hτM : 0 < τ ^ M := by positivity
  rw [Real.log_mul (inv_pos.2 (mul_pos hpi hτM)).ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_inv, Real.log_mul hpi.ne' hτM.ne', Real.log_pow, Real.log_pow]
  ring

lemma ml_pos {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θ : Fin P → ℂ) (hr : residual y s θ ≠ 0) : 0 < residSq y s θ ∧ 0 < (M : ℝ) := by
  obtain ⟨m, hm⟩ : ∃ m, residual y s θ m ≠ 0 := by
    by_contra h; push_neg at h; exact hr (funext h)
  have h1 : 0 < residSq y s θ := by
    unfold residSq
    exact lt_of_lt_of_le (Complex.normSq_pos.2 hm)
      (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ m))
  refine ⟨h1, ?_⟩
  have : 0 < M := Fin.pos m
  exact_mod_cast this

lemma ml_gap {M : ℝ} (hM : 0 < M) (v τ : ℝ) (hv : 0 < v) (hτ : 0 < τ) :
    -M * Real.log τ - M * v / τ ≤ -M * Real.log v - M * v / v ∧
    (τ ≠ v → -M * Real.log τ - M * v / τ < -M * Real.log v - M * v / v) := by
  have hx : 0 < v / τ := div_pos hv hτ
  have hlog : Real.log (v / τ) = Real.log v - Real.log τ := Real.log_div hv.ne' hτ.ne'
  have hvv : M * v / v = M := by field_simp
  have e : (-M * Real.log v - M * v / v) - (-M * Real.log τ - M * v / τ) =
      M * ((v / τ - 1) - Real.log (v / τ)) := by
    rw [hlog, hvv]; field_simp; ring
  constructor
  · have := Real.log_le_sub_one_of_pos hx
    have : 0 ≤ M * ((v / τ - 1) - Real.log (v / τ)) := mul_nonneg hM.le (by linarith)
    linarith
  · intro hne
    have h1 : v / τ ≠ 1 := by
      intro h; apply hne; field_simp at h; linarith
    have := Real.log_lt_sub_one_of_pos hx h1
    have : 0 < M * ((v / τ - 1) - Real.log (v / τ)) := mul_pos hM (by linarith)
    linarith

theorem ml_noise_variance {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θhat : Fin P → ℂ) (hr : residual y s θhat ≠ 0) :
    {σ2 : ℝ | 0 < σ2 ∧ ∀ τ : ℝ, 0 < τ → whiteLogLik τ y s θhat ≤ whiteLogLik σ2 y s θhat} =
      {mlNoiseVar y s θhat} := by
  obtain ⟨hS, hM⟩ := ml_pos y s θhat hr
  set v := mlNoiseVar y s θhat with hvdef
  have hv : 0 < v := div_pos hS hM
  have hSv : residSq y s θhat = (M : ℝ) * v := by rw [hvdef, mlNoiseVar]; field_simp
  have hf : ∀ τ, 0 < τ → whiteLogLik τ y s θhat =
      -(M : ℝ) * Real.log Real.pi + (-(M : ℝ) * Real.log τ - M * v / τ) := by
    intro τ hτ; rw [ml_formula y s θhat τ hτ, hSv]; ring
  ext σ2
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hσ, hmax⟩
    by_contra hne
    have h1 := hmax v hv
    rw [hf v hv, hf σ2 hσ] at h1
    have := (ml_gap hM v σ2 hv hσ).2 hne
    linarith
  · rintro rfl
    refine ⟨hv, fun τ hτ => ?_⟩
    rw [hf τ hτ, hf _ hv]
    have := (ml_gap hM v τ hv hτ).1
    linarith

end Arxiv0810_5751

open Arxiv0810_5751 in
theorem solution {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θhat : Fin P → ℂ) (hr : residual y s θhat ≠ 0) :
    {σ2 : ℝ | 0 < σ2 ∧ ∀ τ : ℝ, 0 < τ → whiteLogLik τ y s θhat ≤ whiteLogLik σ2 y s θhat} =
      {mlNoiseVar y s θhat} :=
  Arxiv0810_5751.ml_noise_variance y s θhat hr
