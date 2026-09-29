-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/58169854-388f-5822-960b-4ecf24b1c7b8

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
import Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme Smooth Flat IsSeparated"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RepresentsRelSubPic algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw BaseChange.ofR baseChange_relativeGroupLaw_mul_compat"
namespace S7hom
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

set_option maxHeartbeats 3200000 in

theorem genericFibreRestrict_mul (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic (baseChange R c K) (sectionBaseChange K ε)
      (algEquivZeroCut (baseChange R c K) (sectionBaseChange K ε)) (D.baseChange K))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε K
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩)).L))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase) :
    genericFibreRestrict R K D.toBase s ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange R c K) (sectionBaseChange K ε)) h').mul (pullback.snd s (specGenericFibreInclusion R K))
        (genericFibreRestrict R K D.toBase s x) (genericFibreRestrict R K D.toBase s y) := by
  have hψ : pullback.fst s (specGenericFibreInclusion R K) ≫ s =
      pullback.snd s (specGenericFibreInclusion R K) ≫ specMap R K := pullback.condition
  have key := baseChange_relativeGroupLaw_mul_compat R c ε D h K h' hP
    (pullback.snd s (specGenericFibreInclusion R K))
    (genericFibreRestrict R K D.toBase s x) (genericFibreRestrict R K D.toBase s y)
    (GoodReductionJacobian.schemeHomOverComp (pullback.fst s (specGenericFibreInclusion R K)) hψ x)
    (GoodReductionJacobian.schemeHomOverComp (pullback.fst s (specGenericFibreInclusion R K)) hψ y)
    (by rw [GoodReductionJacobian.schemeHomOverComp_coe]; exact (genericFibreRestrict_coe_comp_fst (f := D.toBase) (g := s) x).symm)
    (by rw [GoodReductionJacobian.schemeHomOverComp_coe]; exact (genericFibreRestrict_coe_comp_fst (f := D.toBase) (g := s) y).symm)
  rw [← (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul_natural s _ (pullback.fst s (specGenericFibreInclusion R K)) hψ x y,
    GoodReductionJacobian.schemeHomOverComp_coe] at key
  symm
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [key]; exact (genericFibreRestrict_coe_comp_fst (f := D.toBase) (g := s) _).symm
  · rw [((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange R c K) (sectionBaseChange K ε)) h').mul _ _ _).2]
    exact (genericFibreRestrict_coe_comp_snd (f := D.toBase) (g := s) ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y)).symm

theorem schemeHomOverComp_testComp {B T T' X : Scheme.{u}} {s : T ⟶ B} {s' : T' ⟶ B} {f : X ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ s = s') (x : SchemeHomOver s f) (φ : SchemeHomOver f f) :
    NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp ψ hψ x) φ =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp x φ) :=
  Subtype.ext (Category.assoc _ _ _)

set_option maxHeartbeats 3200000 in

theorem main (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic (baseChange R c K) (sectionBaseChange K ε)
      (algEquivZeroCut (baseChange R c K) (sectionBaseChange K ε)) (D.baseChange K))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε K
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩)).L))
    [Smooth D.toBase] [IsSeparated D.toBase] (hN : NeronModelPropertyBundle R K D.toBase)
    (φη : SchemeHomOver (D.baseChange K).toBase (D.baseChange K).toBase)
    (hhom : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver s (D.baseChange K).toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange R c K) (sectionBaseChange K ε)) h').mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange R c K) (sectionBaseChange K ε)) h').mul s (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase) :
    NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) (hN.endExtensionEquiv.symm φη) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s (NeronModelInfra.schemeHomOverComp x (hN.endExtensionEquiv.symm φη))
        (NeronModelInfra.schemeHomOverComp y (hN.endExtensionEquiv.symm φη)) := by
  have hφ : genericFibreRestrict R K D.toBase D.toBase (hN.endExtensionEquiv.symm φη) = φη :=
    hN.restrict_endExtensionEquiv_symm φη

  let s₀ : pullback D.toBase D.toBase ⟶ Spec (CommRingCat.of R) := pullback.fst D.toBase D.toBase ≫ D.toBase
  let p₁ : SchemeHomOver s₀ D.toBase := ⟨pullback.fst D.toBase D.toBase, rfl⟩
  let p₂ : SchemeHomOver s₀ D.toBase := ⟨pullback.snd D.toBase D.toBase, pullback.condition.symm⟩
  haveI : Flat s₀ := inferInstance
  have U0 : NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s₀ p₁ p₂) (hN.endExtensionEquiv.symm φη) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s₀ (NeronModelInfra.schemeHomOverComp p₁ (hN.endExtensionEquiv.symm φη))
        (NeronModelInfra.schemeHomOverComp p₂ (hN.endExtensionEquiv.symm φη)) := by
    apply genericFibreRestrict_injective_of_flat_of_isSeparated R K D.toBase s₀
    have hh := hhom (pullback.snd s₀ (specGenericFibreInclusion R K))
      (genericFibreRestrict R K D.toBase s₀ p₁) (genericFibreRestrict R K D.toBase s₀ p₂)
    rw [genericFibreRestrict_schemeHomOverComp, genericFibreRestrict_mul R K c ε D h h' hP, hφ,
      genericFibreRestrict_mul R K c ε D h h' hP, genericFibreRestrict_schemeHomOverComp,
      genericFibreRestrict_schemeHomOverComp, hφ]

    exact hh

  let ψ : T ⟶ pullback D.toBase D.toBase := pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  have hψ : ψ ≫ s₀ = s := by
    show pullback.lift x.1 y.1 _ ≫ pullback.fst D.toBase D.toBase ≫ D.toBase = s
    rw [pullback.lift_fst_assoc, x.2]
  have hx : GoodReductionJacobian.schemeHomOverComp ψ hψ p₁ = x := Subtype.ext (pullback.lift_fst _ _ _)
  have hy : GoodReductionJacobian.schemeHomOverComp ψ hψ p₂ = y := Subtype.ext (pullback.lift_snd _ _ _)
  rw [← hx, ← hy, ← (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul_natural s₀ s ψ hψ p₁ p₂, schemeHomOverComp_testComp, U0,
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul_natural s₀ s ψ hψ, schemeHomOverComp_testComp, schemeHomOverComp_testComp]

end AlgebraicGeometry.RelPicard.S7hom

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsSeparated D.toBase]
    (hN : NeronModelPropertyBundle R K D.toBase)
    (h' : RepresentsRelSubPic (baseChange R c K) (sectionBaseChange K ε)
      (algEquivZeroCut (baseChange R c K) (sectionBaseChange K ε)) (D.baseChange K))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε K
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩)).L))
    (φη : SchemeHomOver (D.baseChange K).toBase (D.baseChange K).toBase)
    (hhom : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver s (D.baseChange K).toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange R c K) (sectionBaseChange K ε)) h').mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange R c K) (sectionBaseChange K ε)) h').mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη)) :
    ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y)
          (hN.endExtensionEquiv.symm φη) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s
          (NeronModelInfra.schemeHomOverComp x (hN.endExtensionEquiv.symm φη))
          (NeronModelInfra.schemeHomOverComp y (hN.endExtensionEquiv.symm φη)) :=
  fun s x y => AlgebraicGeometry.RelPicard.S7hom.main R K c ε D h h' hP hN φη hhom s x y

end S_AlgebraicGeometry_RelPicard_schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm (solution)
