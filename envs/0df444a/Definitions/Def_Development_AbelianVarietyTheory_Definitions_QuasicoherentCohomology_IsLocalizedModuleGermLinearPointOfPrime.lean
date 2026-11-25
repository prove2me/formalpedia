-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
-- name    : Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:30:30.440621+00:00
-- url     : https://prove2.me/theorems/d812c9ed-1d5b-489c-ba99-83b156ba4bae
-- title:
--   Is Localized Module Germ Linear Point Of Prime
-- statement:
--   Definitions and structural lemmas for Is Localized Module Germ Linear Point Of Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
import Theorems.Thm_GlobalTheory_QCoh_biprodSectionsEquiv_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_hom
import Theorems.Thm_GlobalTheory_SheafLES_res_id
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_map_hom
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_obj_obj
import Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
import Theorems.Thm_P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.biprodSectionsEquiv_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.SheafLES.map_zero_hom
attribute [local simp] GlobalTheory.SheafLES.res_id
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_map_hom
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_obj_obj
attribute [local simp] P2M_GlobalTheory_SheafLES___map_026ec4bafb10
attribute [local simp] P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
namespace GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
section Maps
theorem stalkFunctor_map_germ (φ : F ⟶ G) (x : X) (hx : x ∈ U) (s : Γ(F, U)) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf (F.presheaf.germ U x hx s) =
      G.presheaf.germ U x hx (φ.app U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ.mapPresheaf s
def stalkLinear (φ : F ⟶ G) (x : X) :
    (F.presheaf.stalk x :) →ₗ[X.presheaf.stalk x] (G.presheaf.stalk x :) where
  toFun := (TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf
  map_add' := map_add _
  map_smul' r t := by
    obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
    have hx : x ∈ U ⊓ V := ⟨hU, hV⟩
    rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) x hx,
      ← F.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) x hx, RingHom.id_apply,
      ← germ_smul, stalkFunctor_map_germ, stalkFunctor_map_germ, φ.app_smul, germ_smul]
@[simp]
theorem stalkLinear_germ (φ : F ⟶ G) (x : X) (hx : x ∈ U) (s : Γ(F, U)) :
    stalkLinear φ x (F.presheaf.germ U x hx s) = G.presheaf.germ U x hx (φ.app U s) :=
  stalkFunctor_map_germ φ x hx s
@[simp]
theorem stalkLinear_id (F : X.Modules) (x : X) : stalkLinear (𝟙 F) x = LinearMap.id := by
  ext t
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  rw [stalkLinear_germ]; rfl
@[simp]
theorem stalkLinear_comp (φ : F ⟶ G) (ψ : G ⟶ H) (x : X) :
    stalkLinear (φ ≫ ψ) x = stalkLinear ψ x ∘ₗ stalkLinear φ x := by
  ext t
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  rw [LinearMap.comp_apply, stalkLinear_germ, stalkLinear_germ, stalkLinear_germ]; rfl
def stalkLinearEquiv (e : F ≅ G) (x : X) :
    (F.presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] (G.presheaf.stalk x :) :=
  LinearEquiv.ofLinearMap (stalkLinear e.hom x) (stalkLinear e.inv x)
    (by rw [← stalkLinear_comp, e.inv_hom_id, stalkLinear_id])
    (by rw [← stalkLinear_comp, e.hom_inv_id, stalkLinear_id])
def pointOfPrime (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(X, U)) : U :=
  ⟨hU.fromSpec P, hU.range_fromSpec.le ⟨P, rfl⟩⟩
end Maps
end GlobalTheory.QCoh


