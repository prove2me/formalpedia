-- Prove2me | solution 1 for Arxiv0810_5751.conc_log_lik_eq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:56:59.835055+00:00
-- url     : https://prove2.me/submissions/a21f2c22-f1c2-40e1-ada2-cb14b8ce6131

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

theorem conc_log_lik_eq {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θhat : Fin P → ℂ) (hr : residual y s θhat ≠ 0) :
    whiteLogLik (mlNoiseVar y s θhat) y s θhat = concLogLik y s θhat := by
  obtain ⟨hS, hM⟩ := ml_pos y s θhat hr
  have hv : 0 < mlNoiseVar y s θhat := div_pos hS hM
  rw [ml_formula y s θhat _ hv]
  unfold concLogLik mlNoiseVar
  have : residSq y s θhat / (residSq y s θhat / (M : ℝ)) = M := by field_simp
  rw [this]; ring

end Arxiv0810_5751

open Arxiv0810_5751 in
theorem solution {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θhat : Fin P → ℂ) (hr : residual y s θhat ≠ 0) :
    whiteLogLik (mlNoiseVar y s θhat) y s θhat = concLogLik y s θhat :=
  Arxiv0810_5751.conc_log_lik_eq y s θhat hr
