-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
-- name    : GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:34.484439+00:00
-- url     : https://prove2.me/theorems/5b4c34bd-d081-44f0-978c-ce01ed6bca5a
-- title:
--   Is Invariant Iff Commute Star Projection
-- statement:
--   Definitions and structural lemmas for Is Invariant Iff Commute Star Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap Filter Topology
structure UnitaryRep (G : Type*) [Group G] [TopologicalSpace G] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where

  toHom : G →* unitary (H →L[ℂ] H)

  continuous_orbit' : ∀ v : H, Continuous fun g => (toHom g : H →L[ℂ] H) v
namespace UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
@[coe] noncomputable def op (π : UnitaryRep G H) (g : G) : H →L[ℂ] H := (π.toHom g : H →L[ℂ] H)
noncomputable instance : CoeFun (UnitaryRep G H) (fun _ => G → H →L[ℂ] H) := ⟨op⟩
variable (π : UnitaryRep G H)
lemma continuous_orbit (v : H) : Continuous fun g => π g v := π.continuous_orbit' v
@[simp] lemma map_one : π 1 = 1 := by
  show ((π.toHom 1 : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = 1
  simp
@[simp] lemma map_mul (g h : G) : π (g * h) = π g * π h := by
  show ((π.toHom (g * h) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
    (π.toHom g : H →L[ℂ] H) * (π.toHom h : H →L[ℂ] H)
  simp
lemma map_mul_apply (g h : G) (v : H) : π (g * h) v = π g (π h v) := by
  rw [map_mul]; rfl
@[simp] lemma map_one_apply (v : H) : π 1 v = v := by rw [map_one]; rfl
@[simp] lemma norm_map (g : G) (v : H) : ‖π g v‖ = ‖v‖ := Unitary.norm_map _ v
@[simp] lemma inner_map_map (g : G) (v w : H) : ⟪π g v, π g w⟫_ℂ = ⟪v, w⟫_ℂ :=
  Unitary.inner_map_map _ v w
@[simp] lemma star_map (g : G) : star (π g) = π g⁻¹ := by
  show star ((π.toHom g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
    ((π.toHom g⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
  rw [MonoidHom.map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
@[simp] lemma adjoint_map (g : G) : adjoint (π g) = π g⁻¹ := by
  rw [← star_eq_adjoint, star_map]
@[simp] lemma map_inv_apply_map (g : G) (v : H) : π g⁻¹ (π g v) = v := by
  rw [← map_mul_apply, inv_mul_cancel, map_one_apply]
@[simp] lemma map_apply_map_inv (g : G) (v : H) : π g (π g⁻¹ v) = v := by
  rw [← map_mul_apply, mul_inv_cancel, map_one_apply]
noncomputable def ofLinearIsometryEquiv (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (hρ : ∀ v, Continuous fun g => ρ g v) : UnitaryRep G H where
  toHom := (Unitary.linearIsometryEquiv (𝕜 := ℂ) (H := H)).symm.toMonoidHom.comp ρ
  continuous_orbit' v := by simpa using hρ v
@[simp] lemma ofLinearIsometryEquiv_apply (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (hρ : ∀ v, Continuous fun g => ρ g v) (g : G) (v : H) :
    ofLinearIsometryEquiv ρ hρ g v = ρ g v := rfl
def IsInvariant (V : Submodule ℂ H) : Prop := ∀ (g : G) (v : H), v ∈ V → π g v ∈ V
variable {π}
variable (π) in

def intertwiners (σ : UnitaryRep G K) : Submodule ℂ (H →L[ℂ] K) where
  carrier := {T | ∀ (g : G) (v : H), T (π g v) = σ g (T v)}
  add_mem' {S T} hS hT g v := by simp [hS g v, hT g v]
  zero_mem' g v := by simp
  smul_mem' c T hT g v := by simp [hT g v]
variable {σ : UnitaryRep G K} {τ : UnitaryRep G L}
variable (π σ) in

structure Equiv where

  toLinearIsometryEquiv : H ≃ₗᵢ[ℂ] K

  map_apply' : ∀ (g : G) (v : H), toLinearIsometryEquiv (π g v) = σ g (toLinearIsometryEquiv v)
variable (π σ) in

def IsEquivalent : Prop := Nonempty (π.Equiv σ)
namespace Equiv
def refl (π : UnitaryRep G H) : π.Equiv π := ⟨LinearIsometryEquiv.refl ℂ H, fun _ _ => rfl⟩
def symm (e : π.Equiv σ) : σ.Equiv π where
  toLinearIsometryEquiv := e.toLinearIsometryEquiv.symm
  map_apply' g w := by
    apply e.toLinearIsometryEquiv.injective
    rw [LinearIsometryEquiv.apply_symm_apply, e.map_apply', LinearIsometryEquiv.apply_symm_apply]
def trans (e : π.Equiv σ) (f : σ.Equiv τ) : π.Equiv τ where
  toLinearIsometryEquiv := e.toLinearIsometryEquiv.trans f.toLinearIsometryEquiv
  map_apply' g v := by simp [e.map_apply', f.map_apply']
end Equiv
variable (π) in

def IsIrreducible : Prop :=
  Nontrivial H ∧ ∀ V : Submodule ℂ H, IsClosed (V : Set H) → π.IsInvariant V → V = ⊥ ∨ V = ⊤
section restrict
variable (π) (V : Submodule ℂ H) [CompleteSpace V] (hV : π.IsInvariant V)
noncomputable def restrictAux (g : G) : V ≃ₗᵢ[ℂ] V where
  toFun v := ⟨π g v, hV g v v.2⟩
  invFun v := ⟨π g⁻¹ v, hV _ v v.2⟩
  map_add' v w := Subtype.ext (by simp)
  map_smul' c v := Subtype.ext (by simp)
  left_inv v := Subtype.ext (by simp)
  right_inv v := Subtype.ext (by simp)
  norm_map' v := by simp [Submodule.coe_norm]
noncomputable def restrict : UnitaryRep G V :=
  ofLinearIsometryEquiv
    { toFun := restrictAux π V hV
      map_one' := by ext v; simp [restrictAux]
      map_mul' := fun g h =>
        LinearIsometryEquiv.ext fun v => Subtype.ext (map_mul_apply π g h v) }
    (fun v => (π.continuous_orbit v).subtype_mk _)
end restrict
end UnitaryRep
end GroundTheory.Automorphic


