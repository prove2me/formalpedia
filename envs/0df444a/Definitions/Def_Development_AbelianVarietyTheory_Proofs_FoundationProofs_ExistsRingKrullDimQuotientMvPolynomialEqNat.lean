-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:12.530125+00:00
-- url     : https://prove2.me/theorems/ae1fb29d-5fa9-4d54-a6a1-8cd70121e5df
-- title:
--   Exists Ring Krull Dim Quotient Mv Polynomial Eq Nat
-- statement:
--   Definitions and structural lemmas for Exists Ring Krull Dim Quotient Mv Polynomial Eq Nat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
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
section Graded
variable {A : Type*} [CommRing A] {τ : Type*} [SetLike τ A] [AddSubgroupClass τ A]
  (𝒜 : ℕ → τ) [GradedRing 𝒜]
end Graded
section Poly
variable {σ : Type*}
theorem mem_idealOfVars_pow_of_isHomogeneous {R : Type*} [CommRing R] {p : MvPolynomial σ R}
    {d n : ℕ} (hp : p.IsHomogeneous d) (h : n ≤ d) : p ∈ idealOfVars σ R ^ n := by
  rw [mem_pow_idealOfVars_iff']
  intro x hx
  exact hp.coeff_eq_zero (by omega)
theorem idealOfVars_ne_top {k : Type*} [Field k] : idealOfVars σ k ≠ ⊤ := fun h => by
  have := (mem_pow_idealOfVars_iff' 1 (1 : MvPolynomial σ k)).mp (by simp [h]) 0 (by simp)
  simp at this
variable [Finite σ] {k : Type*} [Field k]
end Poly
section AnyBase
variable {σ ι R S : Type*} [CommRing R] [Fintype ι] [CommRing S] [Algebra R S]
end AnyBase
section Main
variable {σ : Type*} [Finite σ] {k : Type*} [Field k]
example : (Ideal.span {(X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 2))}).IsHomogeneous
      (homogeneousSubmodule (Fin 2) (ZMod 2)) ∧
    Ideal.span {(X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 2))} ≠ ⊤ := by
  have h : (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 2)).IsHomogeneous (1 + 1) :=
    (isHomogeneous_X _ 0).mul (isHomogeneous_X _ 1)
  refine ⟨Ideal.homogeneous_span _ _ (by rintro x rfl; exact ⟨_, h⟩),
    ne_top_of_le_ne_top idealOfVars_ne_top ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, ← pow_one (idealOfVars _ _)]
  exact mem_idealOfVars_pow_of_isHomogeneous h (by norm_num)
end Main
end GlobalTheory


