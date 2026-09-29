-- Prove2me | solution 1 for AutomorphicForm.mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f4e59e2f-90be-5b8d-add3-89bb2f5187d4

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq

set_option autoImplicit false

namespace AutomorphicForm
namespace PrincipalLevelLanding

open NumberField NumberField.AdelicLevel IsDedekindDomain AdelicDock

private abbrev AfQ := FiniteAdeleRing (𝓞 ℚ) ℚ

variable {N : Ideal (𝓞 ℚ)}

private theorem neg_mem_idealBall {y : AfQ} (hy : y ∈ idealBall (𝓞 ℚ) ℚ N) :
    -y ∈ idealBall (𝓞 ℚ) ℚ N := fun v => by
  rw [coe_neg_apply, Valuation.map_neg]; exact hy v

private theorem idealBound_span_singleton {r : 𝓞 ℚ} (hr : r ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    idealBound (𝓞 ℚ) (Ideal.span {r}) v = v.intValuation r := by
  have hN : Ideal.span {r} ≠ (⊥ : Ideal (𝓞 ℚ)) := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [idealBound_of_ne_bot hN, HeightOneSpectrum.intValuation_if_neg _ hr]

private theorem valuedv_ratAlgebraMap_apply (q : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((algebraMap ℚ AfQ q) v) = v.valuation ℚ q := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

section natCast

variable {M : ℕ} (hM : (M : 𝓞 ℚ) ≠ 0)
include hM

private theorem ratValuation_natCast_eq_idealBound (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.valuation ℚ (M : ℚ) = idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v := by
  rw [← map_natCast (algebraMap (𝓞 ℚ) ℚ) M, HeightOneSpectrum.valuation_of_algebraMap,
    idealBound_span_singleton hM]

private theorem idealBound_natCast_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) :
    idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v ≠ 0 := by
  rw [idealBound_span_singleton hM]
  exact v.intValuation_ne_zero _ hM

private theorem idealBound_sq (v : HeightOneSpectrum (𝓞 ℚ)) :
    idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)} ^ 2) v = idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v ^ 2 := by
  rw [Ideal.span_singleton_pow, idealBound_span_singleton (pow_ne_zero 2 hM), map_pow,
    idealBound_span_singleton hM]

private theorem inv_mul_mem_idealBall {y : AfQ} (hy : y ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)} ^ 2)) :
    algebraMap ℚ AfQ ((M : ℚ)⁻¹) * y ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)}) := by
  intro v
  have hyv := hy v
  rw [idealBound_sq hM] at hyv
  rw [coe_mul_apply, Valuation.map_mul, valuedv_ratAlgebraMap_apply, map_inv₀, ratValuation_natCast_eq_idealBound hM]
  calc (idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v)⁻¹ * Valued.v (y v)
      ≤ (idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v)⁻¹ *
          idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v ^ 2 := by gcongr
    _ = idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v := by
          rw [sq, ← mul_assoc, inv_mul_cancel₀ (idealBound_natCast_ne_zero hM v), one_mul]

private theorem natCast_mul_mem_idealBall {y : AfQ} (hy : y ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    algebraMap ℚ AfQ (M : ℚ) * y ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)}) := by
  intro v
  rw [coe_mul_apply, Valuation.map_mul, valuedv_ratAlgebraMap_apply, ratValuation_natCast_eq_idealBound hM]
  calc idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v * Valued.v (y v)
      ≤ idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v * 1 := by
          gcongr; exact valued_apply_le_one hy v
    _ = _ := mul_one _

private theorem mem_idealBall_of_sq {y : AfQ} (hy : y ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)} ^ 2)) :
    y ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)}) := by
  intro v
  have hyv := hy v
  rw [idealBound_sq hM] at hyv
  refine hyv.trans ?_
  calc idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v ^ 2
      = idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v * idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v :=
        sq _
    _ ≤ idealBound (𝓞 ℚ) (Ideal.span {(M : 𝓞 ℚ)}) v * 1 := by
          gcongr; exact idealBound_le_one _ v
    _ = _ := mul_one _

end natCast

private theorem det_finEmbed (g : GL (Fin 2) AfQ) :
    Matrix.GeneralLinearGroup.det (finEmbed (𝓞 ℚ) ℚ g) =
      Units.map (finIncl (𝓞 ℚ) ℚ) (Matrix.GeneralLinearGroup.det g) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply,
    coe_finEmbed]
  refine Prod.ext ?_ ?_
  · show adeleArch (𝓞 ℚ) ℚ (Matrix.det (finMat (𝓞 ℚ) ℚ g)) =
      (finIncl (𝓞 ℚ) ℚ (Matrix.det (g : Matrix (Fin 2) (Fin 2) AfQ))).1
    rw [RingHom.map_det, mapMatrix_arch_finMat, Matrix.det_one, finIncl_apply_fst]
  · show adeleFin (𝓞 ℚ) ℚ (Matrix.det (finMat (𝓞 ℚ) ℚ g)) =
      (finIncl (𝓞 ℚ) ℚ (Matrix.det (g : Matrix (Fin 2) (Fin 2) AfQ))).2
    rw [RingHom.map_det, mapMatrix_fin_finMat, finIncl_apply_snd]

private theorem coe_diagOne (u : AfQˣ) :
    ((diagOne u : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) = Matrix.diagonal ![(u : AfQ), 1] :=
  Matrix.ext fun i j => diagOne_coe_apply u i j

private theorem det_diagOne (u : AfQˣ) : Matrix.GeneralLinearGroup.det (diagOne u) = u := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagOne, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem conj_apply_00 (u w : AfQˣ) (g : Matrix (Fin 2) (Fin 2) AfQ) :
    ((diagOne u : GL (Fin 2) AfQ) * g * (diagOne w : GL (Fin 2) AfQ)) 0 0 = (u : AfQ) * g 0 0 * (w : AfQ) := by
  simp [coe_diagOne, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem conj_apply_01 (u w : AfQˣ) (g : Matrix (Fin 2) (Fin 2) AfQ) :
    ((diagOne u : GL (Fin 2) AfQ) * g * (diagOne w : GL (Fin 2) AfQ)) 0 1 = (u : AfQ) * g 0 1 := by
  simp [coe_diagOne, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem conj_apply_10 (u w : AfQˣ) (g : Matrix (Fin 2) (Fin 2) AfQ) :
    ((diagOne u : GL (Fin 2) AfQ) * g * (diagOne w : GL (Fin 2) AfQ)) 1 0 = g 1 0 * (w : AfQ) := by
  simp [coe_diagOne, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem conj_apply_11 (u w : AfQˣ) (g : Matrix (Fin 2) (Fin 2) AfQ) :
    ((diagOne u : GL (Fin 2) AfQ) * g * (diagOne w : GL (Fin 2) AfQ)) 1 1 = g 1 1 := by
  simp [coe_diagOne, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem diagOne_mul_apply_zero (v : AfQˣ) (g : Matrix (Fin 2) (Fin 2) AfQ) (j : Fin 2) :
    ((diagOne v : GL (Fin 2) AfQ) * g) 0 j = (v : AfQ) * g 0 j := by
  simp [coe_diagOne, Matrix.diagonal_mul]

private theorem diagOne_mul_apply_one (v : AfQˣ) (g : Matrix (Fin 2) (Fin 2) AfQ) (j : Fin 2) :
    ((diagOne v : GL (Fin 2) AfQ) * g) 1 j = g 1 j := by
  simp [coe_diagOne, Matrix.diagonal_mul]

private theorem mul_diagOne_apply_zero (v : AfQˣ) (g : Matrix (Fin 2) (Fin 2) AfQ) (i : Fin 2) :
    (g * (diagOne v : GL (Fin 2) AfQ)) i 0 = g i 0 * (v : AfQ) := by
  simp [coe_diagOne, Matrix.mul_diagonal]

private theorem mul_diagOne_apply_one (v : AfQˣ) (g : Matrix (Fin 2) (Fin 2) AfQ) (i : Fin 2) :
    (g * (diagOne v : GL (Fin 2) AfQ)) i 1 = g i 1 := by
  simp [coe_diagOne, Matrix.mul_diagonal]

private theorem units_mul_mul_inv (u : AfQˣ) (y : AfQ) : (u : AfQ) * y * ((u⁻¹ : AfQˣ) : AfQ) = y := by
  rw [mul_right_comm, Units.mul_inv, one_mul]

private theorem cancel_aux (p q r : ℂ) (hr : r ≠ 0) : r * p * (q * r⁻¹) = p * q :=
  calc r * p * (q * r⁻¹) = r * r⁻¹ * (p * q) := by ring
    _ = p * q := by rw [mul_inv_cancel₀ hr, one_mul]

private theorem forall_fin_two {P : Fin 2 → Fin 2 → Prop} (h00 : P 0 0) (h01 : P 0 1) (h10 : P 1 0)
    (h11 : P 1 1) : ∀ i j, P i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

private theorem twistedTranslate_invariant_of_unit (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (φ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (hK : ∀ (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (k : GL (Fin 2) AfQ),
      (∀ i j, ((k : Matrix (Fin 2) (Fin 2) AfQ) - 1) i j ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)})) →
      (∀ i j, (((k⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) - 1) i j ∈
        idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)})) →
      φ (x * finEmbed (𝓞 ℚ) ℚ k) = φ x)
    (hT : ∀ (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (u : AfQˣ), (u : AfQ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ →
      ((u⁻¹ : AfQˣ) : AfQ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ →
      φ (x * finEmbed (𝓞 ℚ) ℚ (diagOne u)) =
        χ (RatIdele.unitResidue M (Matrix.GeneralLinearGroup.det (finEmbed (𝓞 ℚ) ℚ (diagOne u)))) * φ x)
    (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (k : GL (Fin 2) AfQ)
    (hk : k ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)} ^ 2)) (m : AfQˣ)
    (hmval : (m : AfQ) = algebraMap ℚ AfQ (M : ℚ)) :
    φ (x * finEmbed (𝓞 ℚ) ℚ k * (finEmbed (𝓞 ℚ) ℚ (diagOne m))⁻¹) *
        ((DirichletCharacter.dirichletIdeleChar χ
          (Matrix.GeneralLinearGroup.det (x * finEmbed (𝓞 ℚ) ℚ k)) : ℂˣ) : ℂ) =
      φ (x * (finEmbed (𝓞 ℚ) ℚ (diagOne m))⁻¹) *
        ((DirichletCharacter.dirichletIdeleChar χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) := by
  have hM : (M : 𝓞 ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hminv : ((m⁻¹ : AfQˣ) : AfQ) = algebraMap ℚ AfQ ((M : ℚ)⁻¹) :=
    Units.inv_eq_of_mul_eq_one_left (by rw [hmval, ← map_mul, inv_mul_cancel₀ hMQ, map_one])
  obtain ⟨dk, hdk⟩ : ∃ dk : AfQˣ, dk = Matrix.GeneralLinearGroup.det k := ⟨_, rfl⟩
  have hkmem := (mem_finiteLevelOne_iff).mp hk
  obtain ⟨hk1, hk2⟩ := hkmem
  have hdkval : (dk : AfQ) =
      (k : Matrix (Fin 2) (Fin 2) AfQ) 0 0 * (k : Matrix (Fin 2) (Fin 2) AfQ) 1 1 -
        (k : Matrix (Fin 2) (Fin 2) AfQ) 0 1 * (k : Matrix (Fin 2) (Fin 2) AfQ) 1 0 := by
    rw [hdk, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hdkint : (dk : AfQ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    rw [hdkval]
    exact sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hk1.integral 0 0) (hk1.integral 1 1))
      (mul_mem_integralFiniteAdeles (hk1.integral 0 1) (hk1.integral 1 0))
  have hdkinv : ((dk⁻¹ : AfQˣ) : AfQ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    rw [hdk, ← map_inv, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    exact sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hk2.integral 0 0) (hk2.integral 1 1))
      (mul_mem_integralFiniteAdeles (hk2.integral 0 1) (hk2.integral 1 0))

  have hKK : ((k⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) * (k : Matrix (Fin 2) (Fin 2) AfQ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h00 : ((k⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) 0 0 * (k : Matrix (Fin 2) (Fin 2) AfQ) 0 0 +
      ((k⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) 0 1 * (k : Matrix (Fin 2) (Fin 2) AfQ) 1 0 = 1 := by
    have h := congr_fun (congr_fun hKK 0) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
  have h01 : ((k⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) 0 0 * (k : Matrix (Fin 2) (Fin 2) AfQ) 0 1 +
      ((k⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) 0 1 * (k : Matrix (Fin 2) (Fin 2) AfQ) 1 1 = 0 := by
    have h := congr_fun (congr_fun hKK 0) 1
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide)] at h

  obtain ⟨k', hk'⟩ : ∃ k' : GL (Fin 2) AfQ, k' = diagOne m * ((diagOne dk)⁻¹ * k) * (diagOne m)⁻¹ := ⟨_, rfl⟩
  have hk'mat : (k' : Matrix (Fin 2) (Fin 2) AfQ) =
      (diagOne m : GL (Fin 2) AfQ) * ((diagOne dk⁻¹ : GL (Fin 2) AfQ) * (k : Matrix (Fin 2) (Fin 2) AfQ)) *
        (diagOne m⁻¹ : GL (Fin 2) AfQ) := by
    rw [hk', Units.val_mul, Units.val_mul, Units.val_mul, map_inv, map_inv]
  have hk'inv : ((k'⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) =
      (diagOne m : GL (Fin 2) AfQ) *
        (((k⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) * (diagOne dk : GL (Fin 2) AfQ)) *
        (diagOne m⁻¹ : GL (Fin 2) AfQ) := by
    have hinv : k'⁻¹ = diagOne m * (k⁻¹ * diagOne dk) * (diagOne m)⁻¹ := by
      simp only [hk', mul_inv_rev, inv_inv, mul_assoc]
    rw [hinv, Units.val_mul, Units.val_mul, Units.val_mul, map_inv]
  have hu : ((dk⁻¹ : AfQˣ) : AfQ) * (dk : AfQ) = 1 := Units.inv_mul _

  have hcond1 : ∀ i j, ((k' : Matrix (Fin 2) (Fin 2) AfQ) - 1) i j ∈
      idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)}) := by
    refine forall_fin_two ?_ ?_ ?_ ?_
    · rw [Matrix.sub_apply, hk'mat, conj_apply_00, diagOne_mul_apply_zero, Matrix.one_apply_eq, units_mul_mul_inv]
      have hid : ((dk⁻¹ : AfQˣ) : AfQ) * (k : Matrix (Fin 2) (Fin 2) AfQ) 0 0 - 1 =
          ((dk⁻¹ : AfQˣ) : AfQ) *
            ((k : Matrix (Fin 2) (Fin 2) AfQ) 0 0 * -((k : Matrix (Fin 2) (Fin 2) AfQ) 1 1 - 1) +
              (k : Matrix (Fin 2) (Fin 2) AfQ) 0 1 * (k : Matrix (Fin 2) (Fin 2) AfQ) 1 0) := by
        linear_combination hu - ((dk⁻¹ : AfQˣ) : AfQ) * hdkval
      rw [hid]
      exact mul_mem_idealBall_left hdkinv (add_mem_idealBall
        (mul_mem_idealBall_left (hk1.integral 0 0) (neg_mem_idealBall (mem_idealBall_of_sq hM hk1.lowerRight)))
        (mul_mem_idealBall_left (hk1.integral 0 1) (mem_idealBall_of_sq hM hk1.lowerLeft)))
    · rw [Matrix.sub_apply, hk'mat, conj_apply_01, diagOne_mul_apply_zero, Matrix.one_apply_ne (by decide), sub_zero,
        hmval]
      exact natCast_mul_mem_idealBall hM (mul_mem_integralFiniteAdeles hdkinv (hk1.integral 0 1))
    · rw [Matrix.sub_apply, hk'mat, conj_apply_10, diagOne_mul_apply_one, Matrix.one_apply_ne (by decide), sub_zero,
        hminv, mul_comm]
      exact inv_mul_mem_idealBall hM hk1.lowerLeft
    · rw [Matrix.sub_apply, hk'mat, conj_apply_11, diagOne_mul_apply_one, Matrix.one_apply_eq]
      exact mem_idealBall_of_sq hM hk1.lowerRight
  have hcond2 : ∀ i j, (((k'⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) - 1) i j ∈
      idealBall (𝓞 ℚ) ℚ (Ideal.span {(M : 𝓞 ℚ)}) := by
    refine forall_fin_two ?_ ?_ ?_ ?_
    · rw [Matrix.sub_apply, hk'inv, conj_apply_00, mul_diagOne_apply_zero, Matrix.one_apply_eq, units_mul_mul_inv]
      have hid : ((k⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) 0 0 * (dk : AfQ) - 1 =
          (k : Matrix (Fin 2) (Fin 2) AfQ) 1 1 - 1 := by
        linear_combination (k : Matrix (Fin 2) (Fin 2) AfQ) 1 1 * h00 - (k : Matrix (Fin 2) (Fin 2) AfQ) 1 0 * h01 +
          ((k⁻¹ : GL (Fin 2) AfQ) : Matrix (Fin 2) (Fin 2) AfQ) 0 0 * hdkval
      rw [hid]
      exact mem_idealBall_of_sq hM hk1.lowerRight
    · rw [Matrix.sub_apply, hk'inv, conj_apply_01, mul_diagOne_apply_one, Matrix.one_apply_ne (by decide), sub_zero,
        hmval]
      exact natCast_mul_mem_idealBall hM (hk2.integral 0 1)
    · rw [Matrix.sub_apply, hk'inv, conj_apply_10, mul_diagOne_apply_zero, Matrix.one_apply_ne (by decide), sub_zero,
        hminv, mul_comm]
      exact inv_mul_mem_idealBall hM (mul_mem_idealBall_right hk2.lowerLeft hdkint)
    · rw [Matrix.sub_apply, hk'inv, conj_apply_11, mul_diagOne_apply_one, Matrix.one_apply_eq]
      exact mem_idealBall_of_sq hM hk2.lowerRight

  have hgrp : x * finEmbed (𝓞 ℚ) ℚ k * (finEmbed (𝓞 ℚ) ℚ (diagOne m))⁻¹ =
      x * finEmbed (𝓞 ℚ) ℚ (diagOne dk) * (finEmbed (𝓞 ℚ) ℚ (diagOne m))⁻¹ * finEmbed (𝓞 ℚ) ℚ k' := by
    simp only [hk', map_mul, map_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
  have hcomm : x * finEmbed (𝓞 ℚ) ℚ (diagOne dk) * (finEmbed (𝓞 ℚ) ℚ (diagOne m))⁻¹ =
      x * (finEmbed (𝓞 ℚ) ℚ (diagOne m))⁻¹ * finEmbed (𝓞 ℚ) ℚ (diagOne dk) := by
    have hc : finEmbed (𝓞 ℚ) ℚ (diagOne dk) * finEmbed (𝓞 ℚ) ℚ (diagOne m) =
        finEmbed (𝓞 ℚ) ℚ (diagOne m) * finEmbed (𝓞 ℚ) ℚ (diagOne dk) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm]
    have hc' : finEmbed (𝓞 ℚ) ℚ (diagOne dk) * (finEmbed (𝓞 ℚ) ℚ (diagOne m))⁻¹ =
        (finEmbed (𝓞 ℚ) ℚ (diagOne m))⁻¹ * finEmbed (𝓞 ℚ) ℚ (diagOne dk) := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, hc, inv_mul_cancel_left]
    rw [mul_assoc, hc', ← mul_assoc]

  have hφ1 := hK (x * finEmbed (𝓞 ℚ) ℚ (diagOne dk) * (finEmbed (𝓞 ℚ) ℚ (diagOne m))⁻¹) k' hcond1 hcond2
  have hφ2 := hT (x * (finEmbed (𝓞 ℚ) ℚ (diagOne m))⁻¹) dk hdkint hdkinv

  have hres : RatIdele.unitResidue M (Matrix.GeneralLinearGroup.det (finEmbed (𝓞 ℚ) ℚ (diagOne dk))) =
      RatIdele.unitResidue M (Matrix.GeneralLinearGroup.det (finEmbed (𝓞 ℚ) ℚ k)) := by
    rw [det_finEmbed, det_finEmbed, det_diagOne, hdk]
  have hη := DirichletCharacter.coe_dirichletIdeleChar_apply χ
    (Matrix.GeneralLinearGroup.det (finEmbed (𝓞 ℚ) ℚ k))
  have hne : χ (RatIdele.unitResidue M (Matrix.GeneralLinearGroup.det (finEmbed (𝓞 ℚ) ℚ k))) ≠ 0 := by
    intro h0
    exact (DirichletCharacter.dirichletIdeleChar χ
      (Matrix.GeneralLinearGroup.det (finEmbed (𝓞 ℚ) ℚ k))).ne_zero (by rw [hη, h0, inv_zero])
  rw [hgrp, hφ1, hcomm, hφ2, hres, map_mul, map_mul, Units.val_mul, hη]
  exact cancel_aux _ _ _ hne

end AutomorphicForm.PrincipalLevelLanding

open NumberField NumberField.AdelicLevel IsDedekindDomain AdelicDock AutomorphicForm.PrincipalLevelLanding in

theorem solution
    (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (φ : GL (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) → ℂ)
    (hK : ∀ (x : GL (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
      (k : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)),
      (∀ i j, ((k : Matrix (Fin 2) (Fin 2)
          (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) - 1) i j ∈
        NumberField.AdelicLevel.idealBall (NumberField.RingOfIntegers ℚ) ℚ
          (Ideal.span {(M : NumberField.RingOfIntegers ℚ)})) →
      (∀ i j, (((k⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) - 1) i j ∈
        NumberField.AdelicLevel.idealBall (NumberField.RingOfIntegers ℚ) ℚ
          (Ideal.span {(M : NumberField.RingOfIntegers ℚ)})) →
      φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k) = φ x)
    (hT : ∀ (x : GL (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
      (u : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ),
      (u : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ∈
        NumberField.AdelicLevel.integralFiniteAdeles (NumberField.RingOfIntegers ℚ) ℚ →
      ((u⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
          IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ∈
        NumberField.AdelicLevel.integralFiniteAdeles (NumberField.RingOfIntegers ℚ) ℚ →
      φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (NumberField.AdelicLevel.diagOne u)) =
        χ (RatIdele.unitResidue M (Matrix.GeneralLinearGroup.det
          (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (NumberField.AdelicLevel.diagOne u)))) *
          φ x)
    (x : GL (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
    (k : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
    (hk : k ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ
      (Ideal.span {(M : NumberField.RingOfIntegers ℚ)} ^ 2)) :
    φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k *
        (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (NumberField.AdelicLevel.diagOne
          (Units.map (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :
            ℚ →* IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
            (Units.mk0 (M : ℚ) (Nat.cast_ne_zero.mpr (NeZero.ne M)))))⁻¹)) *
        ((DirichletCharacter.dirichletIdeleChar χ (Matrix.GeneralLinearGroup.det
          (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ k)) : ℂˣ) : ℂ) =
      φ (x * (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (NumberField.AdelicLevel.diagOne
          (Units.map (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :
            ℚ →* IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
            (Units.mk0 (M : ℚ) (Nat.cast_ne_zero.mpr (NeZero.ne M)))))⁻¹)) *
        ((DirichletCharacter.dirichletIdeleChar χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) := by
  exact twistedTranslate_invariant_of_unit M χ φ hK hT x k hk _
    (by rw [Units.coe_map, MonoidHom.coe_coe, Units.val_mk0])

end S_AutomorphicForm_mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq
end P2MW
export P2MW.S_AutomorphicForm_mul_dirichletIdeleChar_det_rightTranslate_invariant_levelOne_sq (solution)
