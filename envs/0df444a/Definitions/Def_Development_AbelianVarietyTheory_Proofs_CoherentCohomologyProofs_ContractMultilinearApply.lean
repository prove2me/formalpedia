-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ContractMultilinearApply
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ContractMultilinearApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:37.282109+00:00
-- url     : https://prove2.me/theorems/1893cbe2-3265-4567-b1ab-d5737456fdbf
-- title:
--   Contract Multilinear Apply
-- statement:
--   Definitions and structural lemmas for Contract Multilinear Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ContractMultilinearApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct BigOperators
namespace GlobalTheory.MultilinearContraction
section
variable {ι : Type*} [Fintype ι] [dι : DecidableEq ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]
omit [Fintype ι] dι in
theorem apply_update (φ : ∀ i, X i →ₗ[R] R) [inst : DecidableEq ι] (x : ∀ i, X i) (k : ι)
    (y : X k) (i : ι) :
    φ i (Function.update x k y i) = Function.update (fun i => φ i (x i)) k (φ k y) i := by
  by_cases h : i = k
  · subst h
    simp
  · simp [Function.update_of_ne h]
def contractMultilinear (φ : ∀ i, X i →ₗ[R] R) (j : ι) : MultilinearMap R X (X j) where
  toFun x := (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j
  map_update_add' := by
    intro inst x k y z
    have h₁ : j ∉ @Finset.erase ι dι Finset.univ j := @Finset.notMem_erase ι dι j Finset.univ
    have h₂ : k ≠ j → k ∈ @Finset.erase ι dι Finset.univ j := fun h =>
      (@Finset.mem_erase ι dι _ _ _).2 ⟨h, Finset.mem_univ _⟩
    generalize @Finset.erase ι dι Finset.univ j = S at h₁ h₂ ⊢
    simp only [apply_update]
    by_cases h : k = j
    · subst h
      simp only [Finset.prod_update_of_notMem h₁,
        Function.update_self, smul_add]
    · have hk := h₂ h
      simp only [Finset.prod_update_of_mem hk, Function.update_of_ne (Ne.symm h), map_add,
        add_mul, add_smul]
  map_update_smul' := by
    intro inst x k c y
    have h₁ : j ∉ @Finset.erase ι dι Finset.univ j := @Finset.notMem_erase ι dι j Finset.univ
    have h₂ : k ≠ j → k ∈ @Finset.erase ι dι Finset.univ j := fun h =>
      (@Finset.mem_erase ι dι _ _ _).2 ⟨h, Finset.mem_univ _⟩
    generalize @Finset.erase ι dι Finset.univ j = S at h₁ h₂ ⊢
    simp only [apply_update]
    by_cases h : k = j
    · subst h
      simp only [Finset.prod_update_of_notMem h₁,
        Function.update_self]
      exact smul_comm _ _ _
    · have hk := h₂ h
      simp only [Finset.prod_update_of_mem hk, Function.update_of_ne (Ne.symm h), map_smul,
        smul_eq_mul, mul_assoc, mul_smul]
noncomputable def contract (φ : ∀ i, X i →ₗ[R] R) (j : ι) : (⨂[R] i, X i) →ₗ[R] X j :=
  PiTensorProduct.lift (contractMultilinear φ j)
end
section
variable {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]
def prodMultilinear (φ : ∀ i, X i →ₗ[R] R) : MultilinearMap R X R :=
  (MultilinearMap.mkPiAlgebra R ι R).compLinearMap φ
noncomputable def prodForm (φ : ∀ i, X i →ₗ[R] R) : (⨂[R] i, X i) →ₗ[R] R :=
  PiTensorProduct.lift (prodMultilinear φ)
end
end GlobalTheory.MultilinearContraction


