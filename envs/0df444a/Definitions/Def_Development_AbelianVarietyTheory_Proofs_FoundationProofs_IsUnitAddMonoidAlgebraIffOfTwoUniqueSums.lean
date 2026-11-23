-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:29.463985+00:00
-- url     : https://prove2.me/theorems/ab09164b-50fe-4eba-8cb3-29237fdbe2d0
-- title:
--   Is Unit Add Monoid Algebra Iff Of Two Unique Sums
-- statement:
--   Definitions and structural lemmas for Is Unit Add Monoid Algebra Iff Of Two Unique Sums, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_isUnit_eq_single
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply


set_option autoImplicit false
open TensorProduct Coalgebra AddMonoidAlgebra
namespace GlobalTheory
section Units
variable {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X]
noncomputable def monomialUnitHom (A : Type*) [CommRing A] (X : Type*) [AddCommGroup X] :
    Aˣ × Multiplicative X →* (A[X])ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun p => single p.2.toAdd (p.1 : A)
      map_one' := rfl
      map_mul' := fun p q => by simp [single_mul_single] }
@[simp] theorem coe_monomialUnitHom (p : Aˣ × Multiplicative X) :
    (monomialUnitHom A X p : A[X]) = single p.2.toAdd (p.1 : A) := rfl
theorem monomialUnitHom_injective [Nontrivial A] : Function.Injective (monomialUnitHom A X) := by
  classical
  refine (injective_iff_map_eq_one _).2 fun p hp => ?_
  have h : (Finsupp.single p.2.toAdd (p.1 : A)) = Finsupp.single 0 1 :=
    congrArg (fun u : (A[X])ˣ => (u : A[X]).coeff) hp
  rcases (Finsupp.single_eq_single_iff _ _ _ _).1 h with ⟨h1, h2⟩ | ⟨-, h2⟩
  · exact Prod.ext (Units.ext h2) h1
  · exact absurd h2 one_ne_zero
variable [IsDomain A]
theorem isUnit_addMonoidAlgebra_iff_of_twoUniqueSums [TwoUniqueSums X] (f : A[X]) :
    IsUnit f ↔ ∃ (x : X) (a : Aˣ), f = single x (a : A) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨x, c, ⟨a, rfl⟩, e⟩ := ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.isUnit_eq_single h
    exact ⟨x, a, e⟩
  · rintro ⟨x, a, rfl⟩
    exact (monomialUnitHom A X (a, .ofAdd x)).isUnit
variable [Module.Free ℤ X]
theorem isUnit_addMonoidAlgebra_iff (f : A[X]) :
    IsUnit f ↔ ∃ (x : X) (a : Aˣ), f = single x (a : A) :=
  isUnit_addMonoidAlgebra_iff_of_twoUniqueSums f
theorem monomialUnitHom_bijective : Function.Bijective (monomialUnitHom A X) := by
  refine ⟨monomialUnitHom_injective, fun u => ?_⟩
  obtain ⟨x, a, e⟩ := (isUnit_addMonoidAlgebra_iff (u : A[X])).1 u.isUnit
  exact ⟨(a, .ofAdd x), Units.ext e.symm⟩
variable (A X) in

noncomputable def unitsAddMonoidAlgebraEquiv : Aˣ × Multiplicative X ≃* (A[X])ˣ :=
  MulEquiv.ofBijective (monomialUnitHom A X) monomialUnitHom_bijective
end Units
section Coordinates
variable {X : Type*} [Zero X] {N : Type*} [AddCommGroup N]
end Coordinates
section Ring
variable {X : Type*} [Zero X] {A : Type*} [Ring A]
end Ring
section Tensor
variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]
variable {M : Type*} [AddCommGroup M] [Module R M]
noncomputable def hochschildD₀ (ρ : M →ₗ[R] M ⊗[R] H) : M →ₗ[R] M ⊗[R] H :=
  ρ - (TensorProduct.mk R M H).flip 1
noncomputable def hochschildD₁ (ρ : M →ₗ[R] M ⊗[R] H) : M ⊗[R] H →ₗ[R] M ⊗[R] (H ⊗[R] H) :=
  (TensorProduct.assoc R M H H).toLinearMap ∘ₗ ρ.rTensor H - (comul (R := R)).lTensor M +
    ((TensorProduct.mk R H H).flip 1).lTensor M
noncomputable def hochschildD₂ (ρ : M →ₗ[R] M ⊗[R] H) :
    M ⊗[R] (H ⊗[R] H) →ₗ[R] M ⊗[R] (H ⊗[R] (H ⊗[R] H)) :=
  (TensorProduct.assoc R M H (H ⊗[R] H)).toLinearMap ∘ₗ ρ.rTensor (H ⊗[R] H) -
    ((TensorProduct.assoc R H H H).toLinearMap ∘ₗ (comul (R := R)).rTensor H).lTensor M +
    ((comul (R := R)).lTensor H).lTensor M -
    (((TensorProduct.mk R H H).flip 1).lTensor H).lTensor M
variable (R H M) in

noncomputable def trivialCoaction : M →ₗ[R] M ⊗[R] H := (TensorProduct.mk R M H).flip 1
variable {X : Type*} [AddMonoid X]
end Tensor
universe u v w
end GlobalTheory


