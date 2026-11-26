-- Prove2me | solution 1 for Arxiv2205_09423.normalized_blocks_single_scattering
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T01:50:56.532731+00:00
-- url     : https://prove2.me/submissions/7eae9fe3-c261-41c2-b149-1b030bfc61a5

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open Arxiv2205_09423

namespace S75NB

lemma reduce_lin {N : ℕ} (d c : ℂ) (F : Fin N → Fin 3 → Fin 3 → ℂ) (g : Fin N → ℂ)
    (u v : Fin 3 → ℝ) :
    reduce (fun a b => d * (if a = b then 1 else 0) + c * ∑ p, F p a b * g p) u v
      = d • reduce (fun a b => if a = b then 1 else 0) u v + c • ∑ p, g p • reduce (F p) u v := by
  ext m n
  simp only [reduce, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => by ring

lemma dot_nonneg3 (v : Fin 3 → ℝ) : 0 ≤ dotProduct v v := by
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1), mul_self_nonneg (v 2)]

lemma norm_unit (v : Fin 3 → ℝ) (hv : dotProduct v v ≠ 0) :
    dotProduct (normalize v) (normalize v) = 1 := by
  unfold Arxiv2205_09423.normalize vnorm
  rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have h0 := dot_nonneg3 v
  have hs := Real.sq_sqrt h0
  have hp : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.2 (lt_of_le_of_ne h0 (Ne.symm hv))
  field_simp
  linarith

lemma normalize_dot (v w : Fin 3 → ℝ) :
    dotProduct (normalize v) w = (vnorm v)⁻¹ * dotProduct v w := by
  unfold Arxiv2205_09423.normalize; rw [smul_dotProduct, smul_eq_mul]

lemma ePhi_props (e : Fin 3 → ℝ) :
    dotProduct (ePhi e) (ePhi e) = 1 ∧ dotProduct (ePhi e) e = 0 := by
  unfold ePhi
  split_ifs with hc h2
  · simp [dotProduct, Fin.sum_univ_three, hc.2]
  · simp [dotProduct, Fin.sum_univ_three, hc.2]
  · constructor
    · apply norm_unit
      simp only [cross_apply, zhat, dotProduct, Fin.sum_univ_three]
      simp
      intro h
      apply hc
      constructor <;> nlinarith [sq_nonneg (e 0), sq_nonneg (e 1)]
    · rw [normalize_dot, dotProduct_comm, dot_cross_self, mul_zero]

lemma pb_orth (e : Fin 3 → ℝ) (he : dotProduct e e = 1) (m n : Fin 2) :
    dotProduct (polarBasis e m) (polarBasis e n) = if m = n then 1 else 0 := by
  obtain ⟨h1, h2⟩ := ePhi_props e
  have hc : dotProduct (crossProduct (ePhi e) e) (crossProduct (ePhi e) e) = 1 := by
    rw [cross_dot_cross, h1, he, dotProduct_comm e (ePhi e), h2]; ring
  have ht : dotProduct (eTheta e) (eTheta e) = 1 := by
    unfold eTheta; exact norm_unit _ (by rw [hc]; norm_num)
  have htp : dotProduct (eTheta e) (ePhi e) = 0 := by
    unfold eTheta; rw [normalize_dot, dotProduct_comm, dot_self_cross, mul_zero]
  fin_cases m <;> fin_cases n <;>
    simp [polarBasis, ht, htp, h1, dotProduct_comm (ePhi e) (eTheta e)]

lemma reduce_one (u : Fin 3 → ℝ) (hu : dotProduct u u = 1) :
    reduce (fun a b => if a = b then (1 : ℂ) else 0) u u = 1 := by
  ext m n
  have h := pb_orth u hu m n
  unfold dotProduct at h
  have h' : ((∑ a, polarBasis u m a * polarBasis u n a : ℝ) : ℂ) = ((if m = n then 1 else 0 : ℝ) : ℂ) := by
    rw [h]
  push_cast at h'
  simp only [reduce, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.one_apply]
  rw [h']; split_ifs <;> simp

end S75NB

open S75NB in
theorem solution {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid)
    (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) (j i : Fin (2 * Nk + 1)) :
    tNorm K A r j i = tbar K A r j i ∧ rNorm K A r j i = rbar K A r j i := by
  obtain ⟨hk, hmode, -, -, hw⟩ := hK
  have hkz : ∀ i, 0 < K.kz i := fun i => Real.sqrt_pos.2 (by linarith [hmode i])
  have hw0 : 0 < K.w := by rw [hw]; have := hk; positivity
  have hu : ∀ i, dotProduct (K.k⁻¹ • K.kvec i) (K.k⁻¹ • K.kvec i) = 1 := by
    intro i
    have h := Real.sq_sqrt (show 0 ≤ K.k ^ 2 - K.kx i ^ 2 - K.ky i ^ 2 by linarith [hmode i])
    simp only [ModeSet.kvec, ModeSet.kz, dotProduct, Fin.sum_univ_three, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h ⊢
    have hk0 : K.k ≠ 0 := hk.ne'
    field_simp
    nlinarith [h]
  have hsc : ((Real.sqrt (K.kz j / K.kz i) * K.w : ℝ) : ℂ) *
      ((2 * Real.pi * K.k * K.kz j : ℝ) : ℂ)⁻¹ = ((K.cji j i : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    unfold ModeSet.cji
    have h1 := hkz j; have h2 := hkz i
    rw [Real.sqrt_div' _ h2.le, Real.sqrt_mul h1.le]
    have s1 : 0 < Real.sqrt (K.kz j) := Real.sqrt_pos.2 h1
    have s2 : 0 < Real.sqrt (K.kz i) := Real.sqrt_pos.2 h2
    have e1 := Real.sq_sqrt h1.le
    have hp := Real.pi_pos
    field_simp
    exact e1
  constructor
  · have hT : tMat3 K A r j i = fun a b => (if i = j then (K.w : ℂ)⁻¹ else 0) *
        (if a = b then 1 else 0) + ((2 * Real.pi * K.k * K.kz j : ℝ) : ℂ)⁻¹ *
        ∑ p, A p (K.k⁻¹ • K.kvec j) (K.k⁻¹ • K.kvec i) a b *
          Complex.exp (Complex.I * ((dotProduct (K.kvec i - K.kvec j) (r p) : ℝ) : ℂ)) := by
      funext a b; unfold tMat3; split_ifs <;> simp
    unfold tNorm tbar blockSum ampRed
    rw [hT, reduce_lin, smul_add, smul_smul, smul_smul, hsc]
    congr 1
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, reduce_one _ (hu i), if_pos rfl, div_self (hkz i).ne', Real.sqrt_one,
        one_mul, ← Complex.ofReal_inv]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hw0.ne', Complex.ofReal_one, one_smul]
    · rw [if_neg hij, if_neg hij, mul_zero, zero_smul]
  · have hR : rMat3 K A r j i = fun a b => (0 : ℂ) *
        (if a = b then 1 else 0) + ((2 * Real.pi * K.k * K.kz j : ℝ) : ℂ)⁻¹ *
        ∑ p, A p (K.k⁻¹ • K.kvecT j) (K.k⁻¹ • K.kvec i) a b *
          Complex.exp (Complex.I * ((dotProduct (K.kvec i - K.kvecT j) (r p) : ℝ) : ℂ)) := by
      funext a b; unfold rMat3; simp
    unfold rNorm rbar blockSum ampRed
    rw [hR, reduce_lin, smul_add, smul_smul, smul_smul, hsc, mul_zero, zero_smul, zero_add]
