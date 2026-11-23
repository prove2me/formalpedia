-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
-- name    : Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:46.098842+00:00
-- url     : https://prove2.me/theorems/14e79e96-37cc-4c8c-beb5-0f8f77687fa4
-- title:
--   Differentiable To Continuous Linear Map
-- statement:
--   Definitions and structural lemmas for Differentiable To Continuous Linear Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open Module
section Defs
variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
def isoTransvection (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) (b : R) : M ≃ₗ[R] M :=
  LinearEquiv.transvection (f := b • h.flip x) (v := x) (by simp [hx])
namespace isoTransvection
variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
theorem apply (b : R) (v : M) : isoTransvection h x hx b v = v + (b * h v x) • x := rfl
theorem coe_toLinearMap (b : R) :
    (isoTransvection h x hx b : M →ₗ[R] M) = LinearMap.transvection (b • h.flip x) x := rfl
@[simp] theorem zero : isoTransvection h x hx 0 = 1 := by
  ext v; simp [apply]
@[simp] theorem apply_self (b : R) : isoTransvection h x hx b x = x := by
  simp [apply, hx]
@[simp] theorem form_apply_self (b : R) (v : M) :
    h (isoTransvection h x hx b v) x = h v x := by
  simp [apply, hx]
@[simp] theorem form_self_apply (b : R) (v : M) :
    h x (isoTransvection h x hx b v) = h x v := by
  simp [apply, hx]
theorem apply_apply (b b' : R) (v : M) :
    isoTransvection h x hx b (isoTransvection h x hx b' v) = isoTransvection h x hx (b + b') v := by
  rw [apply, form_apply_self, apply, apply, add_mul, add_smul, add_assoc, add_comm ((b' * _) • x)]
theorem mul (b b' : R) :
    isoTransvection h x hx b * isoTransvection h x hx b' = isoTransvection h x hx (b + b') := by
  ext v; exact apply_apply h x hx b b' v
theorem inv (b : R) : (isoTransvection h x hx b)⁻¹ = isoTransvection h x hx (-b) :=
  inv_eq_of_mul_eq_one_right (by rw [mul, add_neg_cancel, zero])
theorem symm (b : R) : (isoTransvection h x hx b).symm = isoTransvection h x hx (-b) :=
  inv h x hx b
end isoTransvection
def isoTransvectionHom (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) :
    Multiplicative R →* (M ≃ₗ[R] M) where
  toFun b := isoTransvection h x hx b.toAdd
  map_one' := isoTransvection.zero h x hx
  map_mul' b b' := (isoTransvection.mul h x hx b.toAdd b'.toAdd).symm
@[simp] theorem isoTransvectionHom_apply (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
    (b : Multiplicative R) :
    isoTransvectionHom h x hx b = isoTransvection h x hx b.toAdd := rfl
namespace isoTransvection
variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
variable {h}
variable (h)
theorem det_toLinearMap [Module.Free R M] [Module.Finite R M] (b : R) :
    LinearMap.det (isoTransvection h x hx b : M →ₗ[R] M) = 1 := by
  rw [coe_toLinearMap, LinearMap.transvection.det]
  simp [hx]
theorem det [Module.Free R M] [Module.Finite R M] (b : R) :
    LinearEquiv.det (isoTransvection h x hx b) = 1 := by
  rw [← Units.val_inj, LinearEquiv.coe_det, det_toLinearMap, Units.val_one]
section Lattice
variable {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Module R₀ M] [IsScalarTower R₀ R M]
end Lattice
end isoTransvection
end Defs
section Complex
namespace isoTransvection
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} (x : W)
  (hx : h x x = 0)
end isoTransvection
namespace isoTransvection
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x : W)
  (hx : h x x = 0)
end isoTransvection
end Complex
section Example
noncomputable def hyp : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun u v => u.1 * star v.2 + u.2 * star v.1)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)
example (b : ℂ) : (∀ u v, hyp v u = star (hyp u v)) ∧
    isoTransvection hyp (1, 0) (by simp [hyp]) b (0, 1) = (b, 1) := by
  refine ⟨fun u v => ?_, ?_⟩
  · simp [hyp]; ring
  · simp [isoTransvection.apply, hyp]
end Example
end GlobalTheory


