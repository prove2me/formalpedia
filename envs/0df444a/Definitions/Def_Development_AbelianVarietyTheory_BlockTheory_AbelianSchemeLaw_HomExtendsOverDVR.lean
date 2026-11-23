-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_HomExtendsOverDVR
-- name    : Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_HomExtendsOverDVR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:48.656831+00:00
-- url     : https://prove2.me/theorems/4156c853-fd07-4bd1-a859-cf30041b102d
-- title:
--   Hom Extends Over DVR
-- statement:
--   Definitions and structural lemmas for Hom Extends Over DVR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/HomExtendsOverDVR.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR
noncomputable abbrev genericPt (T K : Type) [CommRing T] [Field K] [Algebra T K] :
    Spec (.of K) ⟶ Spec (.of T) :=
  Spec.map (CommRingCat.ofHom (algebraMap T K))
def HomExtendsOverDVR : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (K : Type) [Field K] [Algebra T K] [IsFractionRing T K]
    (G G' : Over (Spec (.of T))) [GrpObj G] [GrpObj G'],
    ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G' →
    ∀ f : (Over.pullback (genericPt T K)).obj G ⟶ (Over.pullback (genericPt T K)).obj G',
      IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (genericPt T K)).map F = f
example (T K : Type) [CommRing T] [Field K] [Algebra T K]
    (G G' : Over (Spec (.of T))) [GrpObj G] [GrpObj G'] (F : G ⟶ G') [IsMonHom F] :
    IsMonHom ((Over.pullback (genericPt T K)).map F) := inferInstance
example (h : HomExtendsOverDVR) (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (G : Over (Spec (.of T))) [GrpObj G] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G)
    (F : G ⟶ G) [IsMonHom F] (hF : (Over.pullback (genericPt T (FractionRing T))).map F = 𝟙 _) :
    F = 𝟙 G := by
  obtain ⟨F₀, -, hu⟩ := h T (FractionRing T) G G hG hG (𝟙 _) inferInstance
  rw [hu F ⟨inferInstance, hF⟩, hu (𝟙 G) ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩]
end GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR


