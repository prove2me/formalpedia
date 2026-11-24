-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjective
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjective
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:32.688717+00:00
-- url     : https://prove2.me/theorems/8f44930b-cf81-4f32-b83c-e8ba4c97fe89
-- title:
--   First Cohomology Inclusion Tensor Injective
-- statement:
--   Definitions and structural lemmas for First Cohomology Inclusion Tensor Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyInclusionTensorInjective.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
namespace GlobalTheory.CompanionTheory.WedgeOf
section BaseChange
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  (R' : Type) [CommRing R'] [Algebra R R']
@[reducible] def bcF : C ⥤ CommAlgCat.{0} R' where
  obj T := CommAlgCat.of R' (R' ⊗[R] F.obj T)
  map φ := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R' R') (mp F φ))
  map_id T := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun a b ↦
    congrArg (fun y ↦ a ⊗ₜ[R] y) (mp_id F T b))
  map_comp φ ψ := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun a b ↦
    congrArg (fun y ↦ a ⊗ₜ[R] y) (mp_comp F φ ψ b))
def bcM : BC F (bcF F R') where
  α T := (Algebra.TensorProduct.includeRight : F.obj T →ₐ[R] R' ⊗[R] F.obj T).toRingHom
  naturality _ _ := rfl
  smul T r b := by
    change (1 : R') ⊗ₜ[R] (r • b) = algebraMap R R' r • ((1 : R') ⊗ₜ[R] b)
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  bij T := ⟨LinearEquiv.refl _ _, fun _ ↦ rfl⟩
variable {R'} {M : Type} [AddCommGroup M] [Module R M] (j : M →ₗ[R] R')
def ev0 : M ⊗[R] C0 F →ₗ[R] ∀ T : C, R' ⊗[R] F.obj T :=
  LinearMap.pi fun T ↦ TensorProduct.map j (LinearMap.proj T)
def ev1 : M ⊗[R] C1 F →ₗ[R] ∀ (T T' : C) (_ : T ⟶ T'), R' ⊗[R] F.obj T' :=
  LinearMap.pi fun T ↦ LinearMap.pi fun T' ↦ LinearMap.pi fun φ ↦
    TensorProduct.map j ((LinearMap.proj φ) ∘ₗ (LinearMap.proj T') ∘ₗ (LinearMap.proj T))
end BaseChange
end GlobalTheory.CompanionTheory.WedgeOf


