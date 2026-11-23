-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:35.341806+00:00
-- url     : https://prove2.me/theorems/b9cdf622-5092-405e-96f8-1f1ba21fd72a
-- title:
--   Is Affine Hom Of Is Pullback Spec Map
-- statement:
--   Definitions and structural lemmas for Is Affine Hom Of Is Pullback Spec Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
namespace GlobalTheory.QCoh.Qcqs
section Base
variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}
def baseRingHom (p : X ⟶ Spec R) (U : X.Opens) : R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso R).inv ≫ p.appLE ⊤ U le_top
set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_comp_app (g : Y ⟶ X) (p : X ⟶ Spec R) (U : X.Opens) :
    baseRingHom p U ≫ g.app U = baseRingHom (g ≫ p) (g ⁻¹ᵁ U) := by
  rw [baseRingHom, baseRingHom, Category.assoc, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]
theorem app_baseRingHom (g : Y ⟶ X) (p : X ⟶ Spec R) (U : X.Opens) (r : R) :
    g.app U (baseRingHom p U r) = baseRingHom (g ≫ p) (g ⁻¹ᵁ U) r := by
  rw [← baseRingHom_comp_app]; rfl
abbrev baseModule (p : X ⟶ Spec R) (F : X.Modules) (U : X.Opens) : Module R Γ(F, U) :=
  Module.compHom Γ(F, U) (baseRingHom p U).hom
def appLinearBase (p : X ⟶ Spec R) (g : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) (U : X.Opens) :
    letI := baseModule p F U
    letI := baseModule (g ≫ p) G (g ⁻¹ᵁ U)
    Γ(F, U) →ₗ[R] Γ(G, g ⁻¹ᵁ U) :=
  letI := baseModule p F U
  letI := baseModule (g ≫ p) G (g ⁻¹ᵁ U)
  { toFun := φ.app U
    map_add' := map_add _
    map_smul' := fun r s ↦ (φ.app_smul _ s).trans
      congr($(app_baseRingHom g p U r) • (show Γ(G, g ⁻¹ᵁ U) from φ.app U s)) }
def appLinearPreimage (g : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) (U : X.Opens) :
    letI := Module.compHom Γ(G, g ⁻¹ᵁ U) (g.app U).hom
    Γ(F, U) →ₗ[Γ(X, U)] Γ(G, g ⁻¹ᵁ U) :=
  letI := Module.compHom Γ(G, g ⁻¹ᵁ U) (g.app U).hom
  { toFun := φ.app U
    map_add' := map_add _
    map_smul' := fun r s ↦ φ.app_smul r s }
end Base
section Localization
variable {R L : CommRingCat.{u}} [Algebra R L] (S : Submonoid R) [IsLocalization S L]
  {X Y : Scheme.{u}} {p : X ⟶ Spec R} {q : Y ⟶ Spec L} {g : Y ⟶ X}
  (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R L))))
include H
end Localization
end GlobalTheory.QCoh.Qcqs


