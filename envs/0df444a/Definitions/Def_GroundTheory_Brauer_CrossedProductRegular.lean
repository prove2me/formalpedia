-- Prove2me | Definitions.Def_GroundTheory_Brauer_CrossedProductRegular
-- name    : GroundTheory_Brauer_CrossedProductRegular
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:57:01.047871+00:00
-- url     : https://prove2.me/theorems/b9af822b-cb82-4ee7-9b24-56821b434e7a
-- title:
--   Crossed Product Regular
-- statement:
--   Definitions and structural lemmas for Crossed Product Regular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductRegular.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_basis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.CrossedProduct.basis_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Brauer
open groupCohomology TensorProduct
namespace CrossedProduct
section Monomial
variable {G C : Type*} [Fintype G] [DecidableEq G] [Semiring C]
def monomial (π : Equiv.Perm G) (c : G → C) : Matrix G G C :=
  Matrix.of fun i k => if i = π k then c k else 0
omit [Fintype G] in
theorem monomial_apply (π : Equiv.Perm G) (c : G → C) (i k : G) :
    monomial π c i k = if i = π k then c k else 0 := rfl
theorem monomial_mul_monomial (π π' : Equiv.Perm G) (c d : G → C) :
    monomial π c * monomial π' d = monomial (π * π') (fun k => c (π' k) * d k) := by
  ext i k
  simp only [Matrix.mul_apply, monomial_apply, Equiv.Perm.mul_apply]
  rw [Finset.sum_eq_single (π' k)]
  · by_cases h : i = π (π' k) <;> simp [h]
  · intro l _ hl
    simp [hl]
  · simp
omit [Fintype G] in

theorem monomial_one (c : G → C) : monomial 1 c = Matrix.diagonal c := by
  ext i k
  rw [monomial_apply, Matrix.diagonal_apply, Equiv.Perm.one_apply]
  split_ifs with h
  · rw [h]
  · rfl
omit [Fintype G] in
theorem monomial_congr {π π' : Equiv.Perm G} {c c' : G → C} (hπ : π = π') (hc : ∀ k, c k = c' k) :
    monomial π c = monomial π' c' := by
  rw [hπ, funext hc]
end Monomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [DecidableEq (L ≃ₐ[K] L)]
section Diag
variable {C : Type*} [Ring C] [Algebra K C]
def diagHom (d : (L ≃ₐ[K] L) → (L →ₐ[K] C)) : L →ₐ[K] Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) C where
  toFun a := Matrix.diagonal fun ρ => d ρ a
  map_one' := by simp
  map_mul' a b := by simp [Matrix.diagonal_mul_diagonal]
  map_zero' := by simp
  map_add' a b := by simp [Matrix.diagonal_add]
  commutes' c := by
    rw [Matrix.algebraMap_eq_diagonal]
    congr 1
    ext ρ
    simp
theorem diagHom_apply (d : (L ≃ₐ[K] L) → (L →ₐ[K] C)) (a : L) :
    diagHom d a = monomial 1 (fun ρ => d ρ a) := by
  rw [monomial_one]; rfl
end Diag
section Regular
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
variable {C : Type*} [Ring C] [Algebra K C] (j : L →ₐ[K] C)
def regularU (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (σ : L ≃ₐ[K] L) :
    Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) C :=
  monomial (Equiv.mulLeft σ) fun ρ => j ((σ * ρ)⁻¹ (f (σ, ρ) : L))
omit [FiniteDimensional K L] [DecidableEq (L ≃ₐ[K] L)] in

theorem cocycle_apply (hf : IsMulCocycle₂ f) (θ σ τ ρ : L ≃ₐ[K] L) :
    θ (f (σ, τ * ρ) : L) * θ (σ (f (τ, ρ) : L)) = θ (f (σ, τ) : L) * θ (f (σ * τ, ρ) : L) := by
  have h := congrArg (fun x : Lˣ => θ (x : L)) (hf σ τ ρ)
  simp only [Units.val_mul, val_smul_units, map_mul] at h
  linear_combination -h
variable (hf : IsMulCocycle₂ f)
def toMatrix : CrossedProduct hf →ₐ[K] Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) C :=
  lift (diagHom fun ρ => j.comp (ρ⁻¹ : L ≃ₐ[K] L).toAlgHom) (regularU j f)
    (fun σ a => by
      rw [diagHom_apply, diagHom_apply, regularU, monomial_mul_monomial, monomial_mul_monomial]
      refine monomial_congr (by rw [mul_one, one_mul]) fun ρ => ?_
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Equiv.coe_mulLeft,
        Equiv.Perm.one_apply]
      rw [← map_mul, ← map_mul, mul_comm]
      congr 2
      rw [mul_inv_rev, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply σ⁻¹, inv_mul_cancel,
        AlgEquiv.one_apply])
    (fun σ τ => by
      rw [diagHom_apply, regularU, regularU, regularU, monomial_mul_monomial,
        monomial_mul_monomial]
      refine monomial_congr (by ext ρ; simp) fun ρ => ?_
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Equiv.coe_mulLeft]
      rw [← map_mul, ← map_mul]
      congr 1
      have h := cocycle_apply hf (σ * τ * ρ)⁻¹ σ τ ρ
      have e : (τ * ρ)⁻¹ = (σ * τ * ρ)⁻¹ * σ := by group
      rw [e, AlgEquiv.mul_apply, mul_assoc σ τ ρ]
      rw [mul_assoc σ τ ρ] at h
      linear_combination h)
    (by
      rw [diagHom_apply, regularU, Equiv.mulLeft_one]
      refine monomial_congr rfl fun ρ => ?_
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, one_mul]
      rw [map_one_fst_of_isMulCocycle₂ hf])
end Regular
end CrossedProduct
end GroundTheory.Brauer
end


