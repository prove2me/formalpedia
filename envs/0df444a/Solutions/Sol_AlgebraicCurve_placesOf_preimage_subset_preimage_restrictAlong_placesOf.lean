-- Prove2me | solution 1 for AlgebraicCurve.placesOf_preimage_subset_preimage_restrictAlong_placesOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5f20f302-4f18-520a-b268-7b0ba6a0892b

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_placesOf_preimage_subset_preimage_restrictAlong_placesOf

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_placesOf_preimage_subset_preimage_restrictAlong_placesOf.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "placesOf Place Place.ext baseToFunctionField Place.restrictAlong exists_place_range_stalk_eq"
namespace GlueAux
p2m_open "AlgebraicCurve"

theorem comp_algebraMap_stalk_eq
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : X.functionField →+* Y.functionField)
    (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X))
    (y : Y) :
    φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField) =
      (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom := by
  have eX : CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField)) =
      X.presheaf.stalkSpecializes (genericPoint_specializes (π y)) ≫ CommRingCat.ofHom φ := rfl
  have eY : CommRingCat.ofHom ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom) =
      π.stalkMap y ≫ Y.presheaf.stalkSpecializes (genericPoint_specializes y) := rfl
  have key : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField))) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom)) := by
    have l1 : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField))) ≫
        X.fromSpecStalk (π y) = Y.fromSpecStalk (genericPoint Y) ≫ π := by
      rw [eX, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      exact hφπ.symm
    have l2 : Spec.map (CommRingCat.ofHom
        ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom)) ≫
        X.fromSpecStalk (π y) = Y.fromSpecStalk (genericPoint Y) ≫ π := by
      rw [eY, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]
    rw [← cancel_mono (X.fromSpecStalk (π y)), l1, l2]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

theorem place_eq_of_le {K F : Type*} [Field K] [Field F] [Algebra K F] {v w : Place K F}
    (h : v.toValuationSubring ≤ w.toValuationSubring) : v = w :=
  Place.ext (ValuationSubring.eq_of_le_of_ne_top _ h w.ne_top')

theorem eq_restrictAlong_of_range_stalk_eq
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      X.functionField →ₐ[K] Y.functionField)
    (hφ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      φ.toRingHom.IsIntegral)
    (hφπ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      Y.fromSpecStalk (genericPoint Y) ≫ π =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
    (y : Y) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField cY).toAlgebra
    ∀ (w : Place K Y.functionField) (v : Place K X.functionField),
      (algebraMap (Y.presheaf.stalk y) Y.functionField).range = w.toValuationSubring.toSubring →
      (algebraMap (X.presheaf.stalk (π y)) X.functionField).range = v.toValuationSubring.toSubring →
      v = Place.restrictAlong φ hφ w := by
  letI := (baseToFunctionField cX).toAlgebra
  letI := (baseToFunctionField cY).toAlgebra
  intro w v hyw hv
  have hc := comp_algebraMap_stalk_eq π φ.toRingHom hφπ y
  apply place_eq_of_le
  intro f hf
  have hf' : f ∈ (algebraMap (X.presheaf.stalk (π y)) X.functionField).range := by
    rw [hv]; exact hf
  obtain ⟨g, rfl⟩ := RingHom.mem_range.mp hf'
  change φ.toRingHom (algebraMap _ _ g) ∈ w.toValuationSubring
  rw [← RingHom.comp_apply, hc, RingHom.comp_apply, ← ValuationSubring.mem_toSubring, ← hyw]
  exact RingHom.mem_range_self _ _

end AlgebraicCurve.GlueAux

theorem solution
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y] [SmoothOfRelativeDimension 1 cX]
    (π : Y ⟶ X) [UniversallyClosed π]
    (φ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      X.functionField →ₐ[K] Y.functionField)
    (hφ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      φ.toRingHom.IsIntegral)
    (hφπ : letI := (baseToFunctionField cX).toAlgebra
      letI := (baseToFunctionField cY).toAlgebra
      Y.fromSpecStalk (genericPoint Y) ≫ π =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
    (U : X.Opens) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField cY).toAlgebra
    placesOf cY (π ⁻¹ᵁ U) ⊆ (Place.restrictAlong φ hφ) ⁻¹' placesOf cX U := by
  letI := (baseToFunctionField cX).toAlgebra
  letI := (baseToFunctionField cY).toAlgebra
  rintro w ⟨y, hyU, hyc, hyw⟩
  have hxc : IsClosed ({π y} : Set X) := by
    rw [← Set.image_singleton]; exact π.isClosedMap _ hyc
  obtain ⟨v, hv⟩ := exists_place_range_stalk_eq cX (π y) hxc
  refine ⟨π y, hyU, hxc, ?_⟩
  rw [hv, AlgebraicCurve.GlueAux.eq_restrictAlong_of_range_stalk_eq cX cY π φ hφ hφπ y w v hyw hv]

end S_AlgebraicCurve_placesOf_preimage_subset_preimage_restrictAlong_placesOf
end P2MW
export P2MW.S_AlgebraicCurve_placesOf_preimage_subset_preimage_restrictAlong_placesOf (solution)
