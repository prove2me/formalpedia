-- Prove2me | Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
-- name    : GroundTheory_Brauer_CrossedProductMaps
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:07:45.246898+00:00
-- url     : https://prove2.me/theorems/af65bd3a-19de-5d1d-be4c-4fe798b97ed5
-- title:
--   Crossed Product Maps
-- statement:
--   Definitions and structural lemmas for Crossed Product Maps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductMaps.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_basis_apply
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_finrank_eq_sq
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_incl_mul_u
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_incl
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_u
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_one
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
namespace CrossedProduct
open groupCohomology
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}
section lift
variable {A : Type*} [Ring A] [Algebra K A]
def liftAdd (φ : L →ₐ[K] A) (v : (L ≃ₐ[K] L) → A) : CrossedProduct hf →+ A :=
  (Finsupp.liftAddHom fun σ => (AddMonoidHom.mulRight (v σ)).comp (φ : L →+ A)).comp
    coeffAddHom
theorem liftAdd_single (φ : L →ₐ[K] A) (v : (L ≃ₐ[K] L) → A) (σ : L ≃ₐ[K] L) (a : L) :
    liftAdd φ v (single σ a : CrossedProduct hf) = φ a * v σ := by
  simp [liftAdd, coeffAddHom]
def lift (φ : L →ₐ[K] A) (v : (L ≃ₐ[K] L) → A)
    (hcomm : ∀ σ a, v σ * φ a = φ (σ a) * v σ)
    (hmul : ∀ σ τ, v σ * v τ = φ (f (σ, τ)) * v (σ * τ))
    (hone : v 1 = φ (f (1, 1))) : CrossedProduct hf →ₐ[K] A where
  toFun := liftAdd φ v
  map_add' := map_add _
  map_zero' := map_zero _
  map_one' := by
    rw [one_def, liftAdd_single, hone, ← map_mul, Units.inv_mul, map_one]
  map_mul' x y := by
    induction x using induction_on with
    | zero => simp
    | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
    | single σ a =>
    induction y using induction_on with
    | zero => simp
    | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
    | single τ b =>
    rw [single_mul_single, liftAdd_single, liftAdd_single, liftAdd_single, map_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (v σ) (φ b) (v τ), hcomm, mul_assoc (φ (σ b)) (v σ) (v τ), hmul]
  commutes' c := by
    rw [← (incl (hf := hf)).commutes c, incl_apply, liftAdd_single, hone, map_mul, mul_assoc,
      ← map_mul, Units.inv_mul, map_one, mul_one, φ.commutes]
section
variable (φ : L →ₐ[K] A) (v : (L ≃ₐ[K] L) → A) (hcomm : ∀ σ a, v σ * φ a = φ (σ a) * v σ)
    (hmul : ∀ σ τ, v σ * v τ = φ (f (σ, τ)) * v (σ * τ)) (hone : v 1 = φ (f (1, 1)))
@[simp] theorem lift_single (σ : L ≃ₐ[K] L) (a : L) :
    lift (hf := hf) φ v hcomm hmul hone (single σ a) = φ a * v σ :=
  liftAdd_single φ v σ a
@[simp] theorem lift_incl (a : L) : lift (hf := hf) φ v hcomm hmul hone (incl a) = φ a := by
  rw [incl_apply, lift_single, hone, map_mul, mul_assoc, ← map_mul, Units.inv_mul, map_one,
    mul_one]
@[simp] theorem lift_u (σ : L ≃ₐ[K] L) : lift (hf := hf) φ v hcomm hmul hone (u σ) = v σ := by
  rw [u, lift_single, map_one, one_mul]
end
theorem algHom_ext {g₁ g₂ : CrossedProduct hf →ₐ[K] A} (hL : ∀ a, g₁ (incl a) = g₂ (incl a))
    (hu : ∀ σ, g₁ (u σ) = g₂ (u σ)) : g₁ = g₂ := by
  ext x
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single σ a => rw [← incl_mul_u, map_mul, map_mul, hL, hu]
end lift
section coboundary
variable {f' : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
theorem mul_smul_mul_eq_of_coboundary {x : (L ≃ₐ[K] L) → Lˣ}
    (hx : ∀ σ τ : L ≃ₐ[K] L, σ • x τ / x (σ * τ) * x σ = (f' / f) (σ, τ)) (σ τ : L ≃ₐ[K] L) :
    (f (σ, τ) : L) * σ (x τ) * x σ = f' (σ, τ) * x (σ * τ) := by
  have h := hx σ τ
  rw [Pi.div_apply, div_mul_eq_mul_div, div_eq_div_iff_mul_eq_mul] at h
  have h' := congrArg (fun y : Lˣ => (y : L)) h
  simp only [Units.val_mul, val_smul_units] at h'
  linear_combination h'
def equivOfIsMulCoboundary₂ (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (h : IsMulCoboundary₂ (f' / f)) : CrossedProduct hf ≃ₐ[K] CrossedProduct hf' :=
  have key := mul_smul_mul_eq_of_coboundary h.choose_spec
  have hx0 : ∀ σ, ((h.choose σ : Lˣ) : L) ≠ 0 := fun σ => (h.choose σ).ne_zero
  have key1 : (f (1, 1) : L) * h.choose 1 = f' (1, 1) := by
    have k := key 1 1
    rw [AlgEquiv.one_apply, mul_one, mul_assoc, mul_comm (h.choose 1 : L), ← mul_assoc] at k
    exact mul_right_cancel₀ (hx0 1) k
  AlgEquiv.ofAlgHom
    (lift (hf := hf) (incl : L →ₐ[K] CrossedProduct hf')
      (fun σ => (incl (((h.choose σ)⁻¹ : Lˣ) : L) : CrossedProduct hf') * u σ)
      (fun σ a => by
        rw [mul_assoc, u_mul_incl, ← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, mul_comm])
      (fun σ τ => by
        rw [mul_assoc, ← mul_assoc (u σ), u_mul_incl, mul_assoc, u_mul_u, ← mul_assoc,
          ← mul_assoc, ← map_mul, ← map_mul, ← mul_assoc, ← map_mul]
        congr 2
        simp only [Units.val_inv_eq_inv_val, map_inv₀]
        have ea := mul_inv_cancel₀ (hx0 σ)
        have eb := mul_inv_cancel₀ ((map_ne_zero σ).2 (hx0 τ))
        have ec := mul_inv_cancel₀ (hx0 (σ * τ))
        linear_combination
          (-((h.choose σ : L)⁻¹ * (σ (h.choose τ : L))⁻¹ * f' (σ, τ))) * ec -
          ((h.choose σ : L)⁻¹ * (σ (h.choose τ : L))⁻¹ * (h.choose (σ * τ) : L)⁻¹) * key σ τ +
          ((f (σ, τ) : L) * (h.choose (σ * τ) : L)⁻¹ *
            (σ (h.choose τ : L) * (σ (h.choose τ : L))⁻¹)) * ea +
          ((f (σ, τ) : L) * (h.choose (σ * τ) : L)⁻¹) * eb)
      (by
        rw [u_one, ← map_mul, Units.val_inv_eq_inv_val]
        congr 1
        have e1 := inv_mul_cancel₀ (hx0 1)
        linear_combination (-(h.choose 1 : L)⁻¹) * key1 + (f (1, 1) : L) * e1))
    (lift (hf := hf') (incl : L →ₐ[K] CrossedProduct hf)
      (fun σ => (incl (h.choose σ : L) : CrossedProduct hf) * u σ)
      (fun σ a => by
        rw [mul_assoc, u_mul_incl, ← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, mul_comm])
      (fun σ τ => by
        rw [mul_assoc, ← mul_assoc (u σ), u_mul_incl, mul_assoc, u_mul_u, ← mul_assoc,
          ← mul_assoc, ← map_mul, ← map_mul, ← mul_assoc, ← map_mul]
        congr 2
        linear_combination key σ τ)
      (by
        rw [u_one, ← map_mul]
        congr 1
        linear_combination key1))
    (algHom_ext (fun a => by simp) (fun σ => by
      simp only [AlgHom.comp_apply, lift_u, map_mul, lift_incl, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]))
    (algHom_ext (fun a => by simp) (fun σ => by
      simp only [AlgHom.comp_apply, lift_u, map_mul, lift_incl, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]))
@[simp] theorem equivOfIsMulCoboundary₂_incl (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (h : IsMulCoboundary₂ (f' / f)) (a : L) :
    equivOfIsMulCoboundary₂ hf hf' h (incl a) = incl a := by
  simp [equivOfIsMulCoboundary₂]
end coboundary
section split
theorem isMulCocycle₂_one : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) :=
  fun _ _ _ => by simp
def toEnd (hf : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)) :
    CrossedProduct hf →ₐ[K] Module.End K L :=
  lift (Algebra.lmul K L) (fun σ => σ.toLinearMap)
    (fun σ a => by
      ext y
      simp)
    (fun σ τ => by
      ext y
      simp)
    (by
      ext y
      simp)
@[simp] theorem toEnd_single (hf : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ))
    (σ : L ≃ₐ[K] L) (a y : L) : toEnd hf (single σ a) y = a * σ y := by
  simp [toEnd]
variable [FiniteDimensional K L] [IsGalois K L]
theorem toEnd_bijective (hf : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)) :
    Function.Bijective (toEnd hf) := by
  have hinj : Function.Injective (toEnd hf) := RingHom.injective (toEnd hf).toRingHom
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank K (CrossedProduct hf) = Module.finrank K (Module.End K L) := by
    rw [finrank_eq_sq, Module.finrank_linearMap, sq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (toEnd hf).toLinearMap)).1 hinj
def endEquiv (hf : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)) :
    CrossedProduct hf ≃ₐ[K] Module.End K L :=
  AlgEquiv.ofBijective (toEnd hf) (toEnd_bijective hf)
@[simp] theorem endEquiv_apply (hf : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ))
    (x : CrossedProduct hf) : endEquiv hf x = toEnd hf x := rfl
def matrixEquiv (hf : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)) :
    CrossedProduct hf ≃ₐ[K]
      Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K :=
  (endEquiv hf).trans (LinearMap.toMatrixAlgEquiv (Module.finBasis K L))
omit [FiniteDimensional K L] [IsGalois K L] in

theorem isMulCoboundary₂_inv {g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (h : IsMulCoboundary₂ g) :
    IsMulCoboundary₂ g⁻¹ := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x⁻¹, fun σ τ => ?_⟩
  simp only [Pi.inv_apply]
  rw [← hx σ τ, smul_inv']
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
def endEquivOfIsMulCoboundary₂ (hf : IsMulCocycle₂ f) (h : IsMulCoboundary₂ f) :
    CrossedProduct hf ≃ₐ[K] Module.End K L :=
  (equivOfIsMulCoboundary₂ hf isMulCocycle₂_one (by
    rw [one_div]
    exact isMulCoboundary₂_inv h)).trans (endEquiv isMulCocycle₂_one)
end split
end CrossedProduct
end GroundTheory.Brauer
end


