-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:30.418439+00:00
-- url     : https://prove2.me/theorems/224698e9-5e56-4307-abd8-a07202466cd2
-- title:
--   Is Iso App Top Of Is Affine
-- statement:
--   Definitions and structural lemmas for Is Iso App Top Of Is Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace GlobalFunctions
def FibreInjective : Prop :=
  ∀ (R₀ R C₀ C₁ : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R] [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁] [Module.Flat R₀ C₀] [Module.Flat R₀ C₁] (φ : C₀ →ₗ[R₀] C₁), (∀ (k : Type) [Field k] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k], Function.Injective (φ.baseChange k)) → Function.Injective (φ.baseChange R)
def SmoothDescent : Prop :=
  ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] (f g : B →ₐ[R] C) (r : B →ₐ[R] R), ∃ (R₀ B₀ C₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (_ : Algebra R₀ R) (_ : CommRing B₀) (_ : CommRing C₀) (_ : Algebra R₀ B₀) (_ : Algebra R₀ C₀) (f₀ g₀ : B₀ →ₐ[R₀] C₀) (r₀ : B₀ →ₐ[R₀] R₀) (β' : TensorProduct R₀ R B₀ ≃ₐ[R] B) (δ' : TensorProduct R₀ R C₀ ≃ₐ[R] C), Module.Flat R₀ B₀ ∧ Module.Flat R₀ C₀ ∧ ∀ b : B₀, f (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ f₀ b) ∧ g (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ g₀ b) ∧ r (β' (1 ⊗ₜ b)) = algebraMap R₀ R (r₀ b)
section Algebra
end Algebra
section Geometry
variable {R B C : CommRingCat.{0}} {X : Scheme.{0}}
end Geometry
section Core
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  {X : Scheme.{0}}
noncomputable abbrev prR (R k B : Type) [CommRing R] [CommRing k] [CommRing B] [Algebra R k]
    [Algebra R B] : Spec (.of (k ⊗[R] B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := B)).toRingHom)
noncomputable abbrev prL (R k B : Type) [CommRing R] [CommRing k] [CommRing B] [Algebra R k]
    [Algebra R B] : Spec (.of (k ⊗[R] B)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[R] B)))
noncomputable abbrev bc (k : Type) [CommRing k] [Algebra R k] (f : B →ₐ[R] C) :
    CommRingCat.of (k ⊗[R] B) ⟶ CommRingCat.of (k ⊗[R] C) :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k k) f).toRingHom
end Core
section Main
variable {X S T : Scheme.{0}}
end Main
end GlobalFunctions
end GlobalTheory


