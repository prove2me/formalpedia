-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_CupCochains
-- name    : GroundTheory_TateCohomology_CupCochains
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:02.096079+00:00
-- url     : https://prove2.me/theorems/fc6c3f12-14e0-431a-9b87-ba9c8ef4c373
-- title:
--   Cup Cochains
-- statement:
--   Definitions and structural lemmas for Cup Cochains, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct
namespace GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
section Indices
variable {M : Type*} [Monoid M]
variable {α : Type*}
end Indices
section Cochains
variable {A B : Rep k G} {p q n : ℕ}
def cupCochain (h : p + q = n) (f : (Fin p → G) → A) (g : (Fin q → G) → B) :
    (Fin n → G) → (A ⊗ B : Rep k G) := fun x =>
  f (fun i : Fin p => x ⟨i, by omega⟩) ⊗ₜ[k]
    B.ρ (Fin.partialProd x ⟨p, by omega⟩) (g fun j : Fin q => x ⟨p + j, by omega⟩)
theorem cupCochain_apply (h : p + q = n) (f : (Fin p → G) → A) (g : (Fin q → G) → B)
    (x : Fin n → G) :
    cupCochain h f g x = f (fun i : Fin p => x ⟨i, by omega⟩) ⊗ₜ[k]
      B.ρ (Fin.partialProd x ⟨p, by omega⟩) (g fun j : Fin q => x ⟨p + j, by omega⟩) :=
  rfl
def cupₗ (h : p + q = n) :
    ((Fin p → G) → A) →ₗ[k] ((Fin q → G) → B) →ₗ[k] ((Fin n → G) → (A ⊗ B : Rep k G)) :=
  LinearMap.mk₂ k (cupCochain h)
    (fun f f' g => by funext x; simp [cupCochain_apply, TensorProduct.add_tmul])
    (fun c f g => by funext x; simp [cupCochain_apply, TensorProduct.smul_tmul'])
    (fun f g g' => by funext x; simp [cupCochain_apply, TensorProduct.tmul_add])
    (fun c f g => by funext x; simp [cupCochain_apply, TensorProduct.tmul_smul])
variable (A B p q) in

def cupCochainsTensor :
    ((Fin p → G) → A) ⊗[k] ((Fin q → G) → B) →ₗ[k] ((Fin (p + q) → G) → (A ⊗ B : Rep k G)) :=
  TensorProduct.lift (cupₗ rfl)
def oneCochain : (Fin 0 → G) → (𝟙_ (Rep k G) : Rep k G) := fun _ => (1 : k)
end Cochains
end GroundTheory.GroupCoh


