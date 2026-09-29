-- Prove2me | solution 1 for AutomorphicForm.isNormConjugator_one_of_idempotent_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7edacc29-ed37-5294-ada0-6fc25e247a85

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isNormConjugator_one_of_idempotent_orbit

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace AutomorphicForm
p2m_export "AutomorphicForm" "toTensorGL sigmaTensor sigmaGL normString IsNormConjugator"
p2m_open "AutomorphicForm"

namespace NormOfIdempotentOrbit

section Generic

variable {R : Type} [CommRing R]

theorem one_add_smul_mul_one_add_smul (X : Matrix (Fin 2) (Fin 2) R) {r t : R} (h : r * t = 0) :
    (1 + r • X) * (1 + t • X) = 1 + (r + t) • X := by
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, h, zero_smul, add_zero, add_smul, add_assoc]

theorem one_add_smul_mul_one_add_smul_eq_one (X Y : Matrix (Fin 2) (Fin 2) R) {e : R}
    (he : IsIdempotentElem e) (h : X + Y + X * Y = 0) :
    (1 + e • X) * (1 + e • Y) = 1 := by
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, he.eq]
  have hcollect : e • X + (e • Y + e • (X * Y)) = e • (X + Y + X * Y) := by
    rw [smul_add, smul_add, add_assoc]
  rw [add_assoc, hcollect, h, smul_zero, add_zero]

theorem iterate_mul_iterate_eq_zero (s : R →+* R) (e : R) (n : ℕ)
    (horth : ∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0) {i j : ℕ} (hij : i < j) (hj : j < n) :
    (⇑s)^[i] e * (⇑s)^[j] e = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij.le
  rw [Function.iterate_add_apply, ← RingHom.coe_pow, ← map_mul, horth k (by omega) (by omega),
    map_zero]

theorem sum_iterate_mul_iterate_eq_zero (s : R →+* R) (e : R) (n : ℕ)
    (horth : ∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0) {m : ℕ} (hm : m < n) :
    (∑ i ∈ Finset.range m, (⇑s)^[i] e) * (⇑s)^[m] e = 0 := by
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero fun i hi =>
    iterate_mul_iterate_eq_zero s e n horth (Finset.mem_range.mp hi) hm

theorem map_one_add_smul (s : R →+* R) (r : R) (X : Matrix (Fin 2) (Fin 2) R)
    (hX : X.map s = X) : (1 + r • X).map s = 1 + s r • X := by
  rw [Matrix.map_add, Matrix.map_one, Matrix.map_smul', hX]
  · exact map_mul s
  · exact map_zero s
  · exact map_one s
  · exact map_add s

end Generic

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaTensor_includeRight (a : A) :
    sigmaTensor K L A σ (Algebra.TensorProduct.includeRight a) =
      Algebra.TensorProduct.includeRight a := by
  simp [sigmaTensor, Algebra.TensorProduct.includeRight_apply]

theorem map_sigmaTensor_coe_toTensorGL (γ : GL (Fin 2) A) :
    ((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map
        (sigmaTensor K L A σ) =
      ((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
  ext i j
  simp only [toTensorGL, Matrix.map_apply, Matrix.GeneralLinearGroup.map_apply]
  exact sigmaTensor_includeRight K L A σ _

theorem coe_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    ((sigmaGL K L A σ g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (sigmaTensor K L A σ) := rfl

theorem coe_iterate_sigmaGL (δ : GL (Fin 2) (L ⊗[K] A)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (e : L ⊗[K] A)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = 1 + e • X)
    (hX : X.map (sigmaTensor K L A σ) = X) (i : ℕ) :
    (((⇑(sigmaGL K L A σ))^[i] δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      1 + ((⇑(sigmaTensor K L A σ))^[i] e) • X := by
  induction i with
  | zero => simpa using hδ
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coe_sigmaGL, ih,
      map_one_add_smul _ _ _ hX]

theorem coe_prod_range (δ : GL (Fin 2) (L ⊗[K] A)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (e : L ⊗[K] A)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = 1 + e • X)
    (hX : X.map (sigmaTensor K L A σ) = X) (n : ℕ)
    (horth : ∀ i, 0 < i → i < n → e * (⇑(sigmaTensor K L A σ))^[i] e = 0)
    (m : ℕ) (hm : m ≤ n) :
    ((((List.range m).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      1 + (∑ i ∈ Finset.range m, (⇑(sigmaTensor K L A σ))^[i] e) • X := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, Units.val_mul, ih (by omega), coe_iterate_sigmaGL K L A σ δ X e hδ hX,
      one_add_smul_mul_one_add_smul X
        (sum_iterate_mul_iterate_eq_zero (sigmaTensor K L A σ) e n horth (by omega)),
      Finset.sum_range_succ]

theorem exists_isNormConjugator_one (e : L ⊗[K] A) (he : IsIdempotentElem e)
    (horth : ∀ i, 0 < i → i < Module.finrank K L → e * (⇑(sigmaTensor K L A σ))^[i] e = 0)
    (hsum : (∑ i ∈ Finset.range (Module.finrank K L), (⇑(sigmaTensor K L A σ))^[i] e) = 1)
    (γ : GL (Fin 2) A) :
    ∃ δ : GL (Fin 2) (L ⊗[K] A), IsNormConjugator K L A σ γ δ 1 := by
  have hX : (((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) - 1).map
      (sigmaTensor K L A σ) =
      ((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) - 1 := by
    rw [Matrix.map_sub, Matrix.map_one, map_sigmaTensor_coe_toTensorGL]
    · exact map_zero _
    · exact map_one _
    · exact map_sub _
  have hXY : (((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) - 1) +
      ((((toTensorGL K L A γ)⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) - 1) +
      (((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) - 1) *
      ((((toTensorGL K L A γ)⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) - 1) = 0 := by
    have h := Units.mul_inv (toTensorGL K L A γ)
    rw [← sub_eq_zero] at h
    rw [← h]; noncomm_ring
  have hYX : ((((toTensorGL K L A γ)⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) - 1) +
      (((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) - 1) +
      ((((toTensorGL K L A γ)⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) - 1) *
      (((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) - 1) = 0 := by
    have h := Units.inv_mul (toTensorGL K L A γ)
    rw [← sub_eq_zero] at h
    rw [← h]; noncomm_ring
  refine ⟨⟨1 + e • ((toTensorGL K L A γ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) - 1),
    1 + e • ((((toTensorGL K L A γ)⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) - 1),
    one_add_smul_mul_one_add_smul_eq_one _ _ he hXY,
    one_add_smul_mul_one_add_smul_eq_one _ _ he hYX⟩, ?_⟩
  unfold IsNormConjugator
  rw [inv_one, one_mul, mul_one]
  apply Units.ext
  unfold normString
  rw [coe_prod_range K L A σ _ _ e rfl hX (Module.finrank K L) horth (Module.finrank K L) le_rfl,
    hsum, one_smul, add_sub_cancel]

end Twist

end NormOfIdempotentOrbit

end AutomorphicForm

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_isNormConjugator_one_of_idempotent_orbit.AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L)
    (e : L ⊗[K] A) (he : IsIdempotentElem e)
    (horth : ∀ i, 0 < i → i < Module.finrank K L → e * (⇑(sigmaTensor K L A σ))^[i] e = 0)
    (hsum : (∑ i ∈ Finset.range (Module.finrank K L), (⇑(sigmaTensor K L A σ))^[i] e) = 1)
    (γ : GL (Fin 2) A) :
    ∃ δ : GL (Fin 2) (L ⊗[K] A), IsNormConjugator K L A σ γ δ 1 :=
  AutomorphicForm.NormOfIdempotentOrbit.exists_isNormConjugator_one K L A σ e he horth hsum γ

end S_AutomorphicForm_isNormConjugator_one_of_idempotent_orbit
end P2MW
export P2MW.S_AutomorphicForm_isNormConjugator_one_of_idempotent_orbit (solution)
