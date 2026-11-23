-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_StThmA
-- name    : ReciprocityTheory_DualLattices_StThmA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:51.589955+00:00
-- url     : https://prove2.me/theorems/17045eb3-7557-41dd-b410-9cd5fd16eff3
-- title:
--   St Thm A
-- statement:
--   Definitions and structural lemmas for St Thm A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/StThmA.lean

import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
import Theorems.Thm_ReciprocityTheory_PGsh_LHom_sqZero_of_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
def ξmul {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker) :
    (R' : Type u) →ₗ[R₀] π.ker where
  toFun r := ⟨ξ * r, by
    rw [Submodule.restrictScalars_mem] at hξ ⊢
    exact Ideal.mul_mem_right r _ hξ⟩
  map_add' a b := by ext; simp [mul_add]
  map_smul' c r := by ext; simp
namespace BX
variable (B : BX R₀)
def ev {R' : LAlg R₀} (h : B.gg →ₗ[R₀] R') (v : B.gg ⊗[R₀] (R' : Type u)) : R' :=
  LinearMap.mul' R₀ R' (TensorProduct.map h LinearMap.id v)
end BX
def ThmALevelStatement (B : BX R₀) : Prop :=
  ∀ (R' R : LAlg R₀) (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker) (Dp : DualPair R)
    (N : ℕ) (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ})
    (hsq : ξ * ξ = 0),
    (∀ a, a * ξ = 0 → a ∈ Ideal.span {ξ}) → (N : (R' : Type u)) = 0 →
    ∀ (sh th : B.G R') (v w : B.gg ⊗[R₀] (R' : Type u)) (hs ht : B.gg →ₗ[R₀] R')
      (zh : (R' : Type u)ˣ) (z : (R : Type u)ˣ) (c : (R' : Type u)) (e₀ : ℤ),
      N • sh = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) (TensorProduct.map LinearMap.id (ξmul π ξ hξ) v) →
      N • th = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) (TensorProduct.map LinearMap.id (ξmul π ξ hξ) w) →
      B.IsHeight Dp N (B.map π sh) (π.1.toLinearMap ∘ₗ hs) →
      B.IsHeight Dp N (B.map π th) (π.1.toLinearMap ∘ₗ ht) →
      B.IsPairing N (B.map π sh) (B.map π th) z → Units.map (π.1 : R' →* R) zh = z →
      (zh : (R' : Type u)) ^ N = 1 + e₀ * c * ξ →
      π.1 (e₀ * c) = π.1 (B.ev ht v) - π.1 (B.ev hs w)
end ReciprocityTheory.PGsh


