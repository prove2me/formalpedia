-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_CoprimeRegular
-- name    : GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_CoprimeRegular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:52.566711+00:00
-- url     : https://prove2.me/theorems/b1c77a9d-91f3-4689-9a03-d7282ac4b89d
-- title:
--   Coprime Regular
-- statement:
--   Definitions and structural lemmas for Coprime Regular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/CoprimeRegular.lean

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
namespace GroundTheory.ProfCoh
open Representation TensorProduct
section Regular
variable {k Γ N : Type*} [CommRing k] [Group Γ] [Fintype Γ] [DecidableEq Γ] [AddCommGroup N]
  [Module k N] (σ : Representation k Γ N)
noncomputable def regularTensorEquiv : MonoidAlgebra k Γ ⊗[k] N ≃ₗ[k] (Γ →₀ N) :=
  TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv k) (LinearEquiv.refl k N) ≪≫ₗ
    finsuppScalarLeft k N Γ
omit [Group Γ] [Fintype Γ] in
theorem regularTensorEquiv_single_tmul (g : Γ) (r : k) (n : N) :
    regularTensorEquiv (MonoidAlgebra.single g r ⊗ₜ[k] n) = Finsupp.single g (r • n) := by
  ext γ
  simp [regularTensorEquiv, finsuppScalarLeft_apply_tmul_apply, MonoidAlgebra.coeffLinearEquiv,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
omit [Fintype Γ] in

theorem regularTensorEquiv_tprod_apply (h : Γ) (x : MonoidAlgebra k Γ ⊗[k] N) (γ : Γ) :
    regularTensorEquiv (((leftRegular k Γ).tprod σ) h x) γ =
      σ h (regularTensorEquiv x (h⁻¹ * γ)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p n =>
    induction p using MonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq =>
      rw [TensorProduct.add_tmul, map_add, map_add, Finsupp.add_apply, hp, hq, map_add,
        Finsupp.add_apply, map_add]
    | single g r =>
      rw [Representation.tprod_apply, TensorProduct.map_tmul, ofMulAction_single, regularTensorEquiv_single_tmul,
        regularTensorEquiv_single_tmul, Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases hg : h * g = γ
      · subst hg
        simp
      · have : ¬ g = h⁻¹ * γ := fun e => hg (by rw [e, mul_inv_cancel_left])
        simp [hg, this]
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]
omit [Fintype Γ] in
theorem mem_invariants_regular_iff (x : MonoidAlgebra k Γ ⊗[k] N) :
    x ∈ ((leftRegular k Γ).tprod σ).invariants ↔
      ∀ γ, regularTensorEquiv x γ = σ γ (regularTensorEquiv x 1) := by
  rw [mem_invariants]
  constructor
  · intro hx γ
    conv_lhs => rw [← hx γ]
    rw [regularTensorEquiv_tprod_apply, inv_mul_cancel]
  · intro hx h
    apply regularTensorEquiv.injective
    ext γ
    rw [regularTensorEquiv_tprod_apply, hx (h⁻¹ * γ), hx γ, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel_left]
noncomputable def regularInvariantOf : N →ₗ[k] MonoidAlgebra k Γ ⊗[k] N :=
  regularTensorEquiv.symm.toLinearMap ∘ₗ (Finsupp.linearEquivFunOnFinite k N Γ).symm.toLinearMap ∘ₗ
    LinearMap.pi fun γ => σ γ
theorem regularTensorEquiv_regularInvariantOf (n : N) (γ : Γ) :
    regularTensorEquiv (regularInvariantOf σ n) γ = σ γ n := by
  simp [regularInvariantOf]
theorem regularInvariantOf_mem (n : N) :
    regularInvariantOf σ n ∈ ((leftRegular k Γ).tprod σ).invariants := by
  rw [mem_invariants_regular_iff]
  intro γ
  rw [regularTensorEquiv_regularInvariantOf, regularTensorEquiv_regularInvariantOf, map_one,
    Module.End.one_apply]
noncomputable def invariantsLeftRegularTensorEquiv :
    ((leftRegular k Γ).tprod σ).invariants ≃ₗ[k] N where
  toFun x := regularTensorEquiv (x : MonoidAlgebra k Γ ⊗[k] N) 1
  map_add' x y := by simp
  map_smul' c x := by simp
  invFun n := ⟨regularInvariantOf σ n, regularInvariantOf_mem σ n⟩
  left_inv x := by
    apply Subtype.ext
    apply regularTensorEquiv.injective
    ext γ
    simp only
    rw [regularTensorEquiv_regularInvariantOf, ← (mem_invariants_regular_iff σ _).1 x.2 γ]
  right_inv n := by
    simp only
    rw [regularTensorEquiv_regularInvariantOf, map_one, Module.End.one_apply]
end Regular
section Comp
variable {k Γ₁ Γ₂ X : Type*} [CommRing k] [Group Γ₁] [Group Γ₂] [AddCommGroup X] [Module k X]
end Comp
end GroundTheory.ProfCoh


