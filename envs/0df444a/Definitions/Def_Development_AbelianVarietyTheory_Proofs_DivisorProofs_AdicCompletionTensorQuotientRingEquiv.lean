-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:31.070916+00:00
-- url     : https://prove2.me/theorems/60ff6ecf-d6f0-4809-b434-082778513f10
-- title:
--   Adic Completion Tensor Quotient Ring Equiv
-- statement:
--   Definitions and structural lemmas for Adic Completion Tensor Quotient Ring Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
namespace GlobalTheory.AdicSurj
open AdicCompletion
variable (B : Type) {A : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)
theorem pow_le_comap (n : ℕ) :
    J ^ n ≤ ((J.map (algebraMap A B)) ^ n).comap (algebraMap A B) := by
  rw [← Ideal.map_pow]; exact Ideal.le_comap_map
noncomputable def lev (n : ℕ) :
    AdicCompletion J A →+* B ⧸ (J.map (algebraMap A B)) ^ n :=
  (Ideal.quotientMap _ (algebraMap A B) (pow_le_comap B J n)).comp (evalₐ J n).toRingHom
theorem lev_mk (n : ℕ) (s : AdicCauchySequence J A) :
    lev B J n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ (algebraMap A B (s n)) := by
  simp [lev, evalₐ_mk, Ideal.quotientMap_mk]
theorem lev_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow _ hle).comp (lev B J n) = lev B J m := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  have h1 := s.property hle
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  simp only [RingHom.comp_apply, lev_mk]
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
  have h3 : s n - s m ∈ J ^ m := by rw [← neg_sub]; exact neg_mem h1
  exact Ideal.mem_comap.mp (pow_le_comap B J m h3)
noncomputable def psi : AdicCompletion J A →+* AdicCompletion (J.map (algebraMap A B)) B :=
  AdicCompletion.liftRingHom _ (lev B J) (fun hle ↦ lev_compat B J hle)
theorem evalₐ_psi (n : ℕ) (x : AdicCompletion J A) :
    evalₐ _ n (psi B J x) = lev B J n x := by
  simp [psi]
theorem psi_algebraMap (a : A) :
    psi B J (algebraMap A (AdicCompletion J A) a) =
      algebraMap A (AdicCompletion (J.map (algebraMap A B)) B) a := by
  refine ext_evalₐ fun n ↦ ?_
  rw [evalₐ_psi, lev, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk, AdicCompletion.algebraMap_apply, evalₐ_of]
end GlobalTheory.AdicSurj
namespace GlobalTheory.AdicSurj
open AdicCompletion
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)
instance isScalarTower_adic :
    IsScalarTower A B (AdicCompletion (J.map (algebraMap A B)) B) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
noncomputable def psiₐ :
    AdicCompletion J A →ₐ[A] AdicCompletion (J.map (algebraMap A B)) B :=
  { psi B J with commutes' := psi_algebraMap B J }
noncomputable def theta :
    B ⊗[A] AdicCompletion J A →ₐ[B] AdicCompletion (J.map (algebraMap A B)) B :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) (psiₐ J) fun _ _ ↦ Commute.all _ _
end GlobalTheory.AdicSurj


