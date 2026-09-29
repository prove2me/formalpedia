-- Prove2me | solution 1 for AlgebraicGeometry.isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6b0f3a14-169e-541a-bcca-9b62234c1912

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace GDIM1

theorem isIntegral_of_geometricallyIntegral (k : Type u) [Field k] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) [GeometricallyIntegral c] : IsIntegral C :=
  GeometricallyIntegral.geometrically_isIntegral (f := c) (𝟙 _) (𝟙 C) c IsPullback.of_id_fst

theorem locallyOfFiniteType_of_smoothOfRelativeDimension {X Y : Scheme.{u}} (n : ℕ) (f : X ⟶ Y)
    [SmoothOfRelativeDimension n f] : LocallyOfFiniteType f := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  infer_instance

theorem jacobsonSpace_of_field (k : Type u) [Field k] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType c] : JacobsonSpace C :=
  LocallyOfFiniteType.jacobsonSpace c

theorem algebraMap_stalk_surjective_of_eq_genericPoint (C : Scheme.{u}) [IsIntegral C] (x : C)
    (hx : x = genericPoint C) :
    Function.Surjective (algebraMap (C.presheaf.stalk x) C.functionField) := by
  subst hx
  show Function.Surjective (C.presheaf.stalkSpecializes (specializes_refl _)).hom
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.surjective_id

end GDIM1

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] :
    (∀ x : ↥C, IsClosed ({x} : Set ↥C) ∨ IsGenericPoint x (⊤ : Set ↥C)) ∧
    (∃ x : ↥C, ¬ IsGenericPoint x (⊤ : Set ↥C)) := by
  haveI : IsIntegral C := GDIM1.isIntegral_of_geometricallyIntegral k c
  have hgen : IsGenericPoint (genericPoint C) (⊤ : Set C) := genericPoint_spec C
  refine ⟨fun x => ?_, ?_⟩
  · by_cases hx : x = genericPoint C
    · exact Or.inr (hx ▸ hgen)
    · exact Or.inl (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c x hx)
  · haveI : LocallyOfFiniteType c := GDIM1.locallyOfFiniteType_of_smoothOfRelativeDimension 1 c
    haveI : JacobsonSpace C := GDIM1.jacobsonSpace_of_field k c
    obtain ⟨x, -, hx⟩ :=
      nonempty_inter_closedPoints (Set.univ_nonempty (α := C)) isClosed_univ.isLocallyClosed
    refine ⟨x, fun hxg => ?_⟩
    have hxc : IsClosed ({x} : Set C) := mem_closedPoints_iff.mp hx
    letI : Algebra k C.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    obtain ⟨v, hv⟩ := AlgebraicCurve.exists_place_range_stalk_eq c x hxc
    have htop : v.toValuationSubring.toSubring = ⊤ :=
      hv.symm.trans (RingHom.range_eq_top.mpr
        (GDIM1.algebraMap_stalk_surjective_of_eq_genericPoint C x (hxg.eq hgen)))
    exact v.ne_top' (by
      ext y
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      show y ∈ v.toValuationSubring.toSubring
      rw [htop]; exact Subring.mem_top y)

end S_AlgebraicGeometry_isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one (solution)
