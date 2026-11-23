-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:40.264185+00:00
-- url     : https://prove2.me/theorems/b7297e72-ac35-468d-a79a-1768fea13c4f
-- title:
--   Exists Forms Algebraic Independent Smul Sub Sum Mem
-- statement:
--   Definitions and structural lemmas for Exists Forms Algebraic Independent Smul Sub Sum Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
section Forms
variable {σ ι R : Type*} [CommRing R]
variable [Fintype ι]
def formCombinations (I : Ideal (MvPolynomial σ R)) (F : ι → MvPolynomial σ R) (n : ℕ) :
    Submodule R (MvPolynomial σ R) where
  carrier := {p | ∃ G : ι → MvPolynomial σ R, (∀ i, (G i).IsHomogeneous n) ∧
    p - ∑ i, F i * G i ∈ I}
  zero_mem' := ⟨0, fun _ => isHomogeneous_zero _ _ _, by simp⟩
  add_mem' := by
    rintro p q ⟨G, hG, hp⟩ ⟨G', hG', hq⟩
    refine ⟨G + G', fun i => (hG i).add (hG' i), ?_⟩
    convert I.add_mem hp hq using 1
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  smul_mem' := by
    rintro c p ⟨G, hG, hp⟩
    refine ⟨fun i => C c * G i, fun i => by simpa using (isHomogeneous_C σ c).mul (hG i), ?_⟩
    convert I.mul_mem_left (C c) hp using 1
    simp only [smul_eq_C_mul, mul_sub, Finset.mul_sum, mul_left_comm]
end Forms
section Independence
end Independence
section Main
variable {σ : Type*} {o : Type*} [CommRing o]
theorem map_algebraMap_quotient_ne_top [IsDomain o] (I : Ideal (MvPolynomial σ o))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ o))
    [Module.IsTorsionFree o (MvPolynomial σ o ⧸ I)] (hI' : I ≠ ⊤) {J : Ideal o} (hJ : J ≠ ⊤) :
    J.map (algebraMap o (MvPolynomial σ o ⧸ I)) ≠ ⊤ := by
  haveI := Ideal.Quotient.nontrivial_iff.mpr hI'
  have h0 : ∀ p ∈ I, constantCoeff p = 0 := by
    intro p hp
    have h1 := homogeneousComponent_mem_of_mem hI hp 0
    rw [homogeneousComponent_zero, ← Ideal.Quotient.eq_zero_iff_mem] at h1
    have h2 : coeff 0 p • (1 : MvPolynomial σ o ⧸ I) = 0 := by
      rw [← Algebra.algebraMap_eq_smul_one]; exact h1
    exact (smul_eq_zero.mp h2).resolve_right one_ne_zero
  intro h
  apply hJ
  have h3 := congrArg (Ideal.map (Ideal.Quotient.lift I constantCoeff h0)) h
  rw [Ideal.map_map, Ideal.map_top] at h3
  have h4 : (Ideal.Quotient.lift I constantCoeff h0).comp
      (algebraMap o (MvPolynomial σ o ⧸ I)) = RingHom.id o := by
    ext r
    exact constantCoeff_C σ r
  rwa [h4, Ideal.map_id] at h3
variable [Finite σ] [IsDedekindDomain o]
example : (⊥ : Ideal (MvPolynomial (Fin 2) ℤ)).IsHomogeneous (homogeneousSubmodule (Fin 2) ℤ) ∧
    Module.IsTorsionFree ℤ (MvPolynomial (Fin 2) ℤ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℤ))) ∧
    (Ideal.span {(2 : ℤ)}).IsMaximal ∧
    (Ideal.span {(2 : ℤ)}).map
      (algebraMap ℤ (MvPolynomial (Fin 2) ℤ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℤ)))) ≠ ⊤ := by
  have h1 : Module.IsTorsionFree ℤ
      (MvPolynomial (Fin 2) ℤ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℤ))) :=
    Function.Injective.moduleIsTorsionFree _
      (AlgEquiv.quotientBot ℤ (MvPolynomial (Fin 2) ℤ)).injective (fun c x => map_smul _ c x)
  have h2 : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible
  exact ⟨Ideal.IsHomogeneous.bot _, h1, h2,
    map_algebraMap_quotient_ne_top _ (Ideal.IsHomogeneous.bot _) bot_ne_top h2.ne_top⟩
end Main
end GlobalTheory


