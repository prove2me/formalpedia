-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:17.176596+00:00
-- url     : https://prove2.me/theorems/5b2417cd-8be7-43ec-82fc-bb6594c3136c
-- title:
--   Dual Restrict Surjective Of Is Torsion Free Quotient
-- statement:
--   Definitions and structural lemmas for Dual Restrict Surjective Of Is Torsion Free Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
namespace GlobalTheory
section Defs
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
structure IsSymplecticFamily (B : LinearMap.BilinForm R M) (e f : ι → M) (d : ι → R) : Prop where
  left_left : ∀ i j, B (e i) (e j) = 0
  right_right : ∀ i j, B (f i) (f j) = 0
  left_right_self : ∀ i, B (e i) (f i) = d i
  left_right_ne : ∀ i j, i ≠ j → B (e i) (f j) = 0
def IsSymplecticBasisOfType (B : LinearMap.BilinForm R M) (b : Basis (ι ⊕ ι) R M) (d : ι → R) :
    Prop :=
  IsSymplecticFamily B (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i)) d
def IsSymplecticBasis (B : LinearMap.BilinForm R M) (b : Basis (ι ⊕ ι) R M) : Prop :=
  IsSymplecticBasisOfType B b fun _ => 1
noncomputable def standardAltForm [Fintype ι] [DecidableEq ι] (d : ι → R) :
    LinearMap.BilinForm R (ι ⊕ ι → R) :=
  Matrix.toBilin' (Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0)
namespace IsSymplecticFamily
variable {B : LinearMap.BilinForm R M} {e f : ι → M} {d : ι → R}
end IsSymplecticFamily
end Defs
section Frobenius
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M]
end Frobenius
section BasisLemmas
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {B : LinearMap.BilinForm R M}
namespace IsSymplecticBasisOfType
variable {b : Basis (ι ⊕ ι) R M} {d : ι → R}
theorem reindex {κ : Type*} (h : IsSymplecticBasisOfType B b d) (σ : ι ≃ κ) :
    IsSymplecticBasisOfType B (b.reindex (σ.sumCongr σ)) fun k => d (σ.symm k) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
  · simpa using IsSymplecticFamily.left_left h _ _
  · simpa using IsSymplecticFamily.right_right h _ _
  · simpa using IsSymplecticFamily.left_right_self h _
  · simpa using IsSymplecticFamily.left_right_ne h _ _ (σ.symm.injective.ne hij)
end IsSymplecticBasisOfType
namespace IsSymplecticBasis
variable {b : Basis (ι ⊕ ι) R M}
end IsSymplecticBasis
end BasisLemmas
section Existence
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Free R M] [Module.Finite R M] {B : LinearMap.BilinForm R M}
end Existence
section Isotropic
section Maps
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
def quotientOrthogonalToDual (B : LinearMap.BilinForm R M) (hB : B.IsAlt) (I : Submodule R M) :
    (M ⧸ B.orthogonal I) →ₗ[R] Dual R I :=
  (B.orthogonal I).liftQ (I.dualRestrict ∘ₗ B) fun _ hy =>
    LinearMap.ext fun x => hB.eq_iff.1 (hy x x.2)
@[simp]
theorem quotientOrthogonalToDual_mk (B : LinearMap.BilinForm R M) (hB : B.IsAlt)
    (I : Submodule R M) (y : M) (x : I) :
    quotientOrthogonalToDual B hB I (Submodule.Quotient.mk y) x = B y x := rfl
def orthogonalQuotientForm (B : LinearMap.BilinForm R M) (hB : B.IsAlt) (I : Submodule R M) :
    LinearMap.BilinForm R (B.orthogonal I ⧸ I.submoduleOf (B.orthogonal I)) :=
  LinearMap.liftQ₂ _ _ (B.restrict (B.orthogonal I))
    (fun x hx => LinearMap.ext fun y => y.2 x hx)
    (fun x hx => LinearMap.ext fun y => hB.eq_iff.1 (y.2 x hx))
end Maps
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Finite R M] {B : LinearMap.BilinForm R M} {I : Submodule R M}
end Isotropic
end GlobalTheory


