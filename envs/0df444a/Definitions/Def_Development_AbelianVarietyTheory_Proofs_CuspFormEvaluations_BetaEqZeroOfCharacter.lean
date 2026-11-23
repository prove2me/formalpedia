-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:07.006794+00:00
-- url     : https://prove2.me/theorems/a2a73130-30ac-4db0-9b12-64b7ce46d830
-- title:
--   Beta Eq Zero Of Character
-- statement:
--   Definitions and structural lemmas for Beta Eq Zero Of Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace GlobalTheory.LagSplit
section Defs
variable {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V]
def IsLagSection (ω : LinearMap.BilinForm R M) (π : M →ₗ[R] V) (σ : V →ₗ[R] M) : Prop :=
  (∀ z, π (σ z) = z) ∧ ∀ z w, ω (σ z) (σ w) = 0
def KerIsotropic (ω : LinearMap.BilinForm R M) (π : M →ₗ[R] V) : Prop :=
  ∀ m m', π m = 0 → π m' = 0 → ω m m' = 0
def beta (ω : LinearMap.BilinForm R M) (σ σ' : V →ₗ[R] M) : LinearMap.BilinForm R V :=
  LinearMap.compl₁₂ ω σ σ'
@[simp] theorem beta_apply (ω : LinearMap.BilinForm R M) (σ σ' : V →ₗ[R] M) (z w : V) :
    beta ω σ σ' z w = ω (σ z) (σ' w) := rfl
end Defs
section Concrete
variable {g : ℕ}
def omegaCx (g : ℕ) : LinearMap.BilinForm ℂ (Fin g ⊕ Fin g → ℂ) :=
  LinearMap.mk₂ ℂ (fun a b => ∑ i, (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i)))
    (fun a a' b => by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by simp; ring)
    (fun c a b => by
      rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring)
    (fun a b b' => by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by simp; ring)
    (fun c a b => by
      rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring)
def perProj (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun u := u ∘ Sum.inl + τ *ᵥ (u ∘ Sum.inr)
  map_add' u v := by
    have h1 : (u + v) ∘ Sum.inl = u ∘ Sum.inl + v ∘ Sum.inl := rfl
    have h2 : (u + v) ∘ Sum.inr = u ∘ Sum.inr + v ∘ Sum.inr := rfl
    rw [h1, h2, Matrix.mulVec_add]; abel
  map_smul' c u := by
    have h1 : (c • u) ∘ Sum.inl = c • (u ∘ Sum.inl) := rfl
    have h2 : (c • u) ∘ Sum.inr = c • (u ∘ Sum.inr) := rfl
    rw [h1, h2, Matrix.mulVec_smul, smul_add]; rfl
def secL (g : ℕ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ) where
  toFun z := Sum.elim z 0
  map_add' z w := by ext (i | i) <;> simp
  map_smul' c z := by ext (i | i) <;> simp
def secH (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ) where
  toFun z := Sum.elim (-(τ.map star *ᵥ (((2 * I) • imC τ)⁻¹ *ᵥ z))) (((2 * I) • imC τ)⁻¹ *ᵥ z)
  map_add' z w := by ext (i | i) <;> simp [Matrix.mulVec_add, add_comm]
  map_smul' c z := by ext (i | i) <;> simp [Matrix.mulVec_smul]
end Concrete
section General
variable {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V]
  {ω : LinearMap.BilinForm R M} {π : M →ₗ[R] V} {σ σ' σ'' : V →ₗ[R] M}
variable {O : Type*} [CommRing O] [StarRing O] [Module O M] [Module O V]
end General
end GlobalTheory.LagSplit


