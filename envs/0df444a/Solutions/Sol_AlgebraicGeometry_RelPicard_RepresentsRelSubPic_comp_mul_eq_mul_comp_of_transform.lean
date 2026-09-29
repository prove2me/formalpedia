-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a100c6e3-59c3-5e97-9887-6555b99e0601

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform.AlgebraicGeometry.RelPicard"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme RelPicard.RepresentsRelSubPic"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "postComp RigidifiedLineBundle RigidifiedLineBundle.unit RigidifiedLineBundle.Classes RepresentsRelSubPic RigidifiedLineBundle.tensor_congr SubPicGroupCondition RepresentsRelSubPic.homEquiv_mul"
namespace RepresentsRelSubPic
p2m_export "AlgebraicGeometry.RelPicard.RepresentsRelSubPic" "classify classify_spec classify_unique ext_of_iso poincare zero poincare_mem mk grpObj relativeGroupLaw homEquiv_mul representableBy"
p2m_open "AlgebraicGeometry.RelPicard.RepresentsRelSubPic AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {P : SubPicGroupCondition c ε} {P' : SubPicGroupCondition c' ε'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    (h' : RepresentsRelSubPic c' ε' P'.toSubPicCondition D')
    (Φ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      RigidifiedLineBundle c' ε' t → RigidifiedLineBundle c ε t)
    (hcut : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t),
      P'.P t M → P.P t (Φ t M))
    (φ : SchemeHomOver D'.toBase D.toBase)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
        (hM : P'.P t M),
        postComp φ (h'.classify t M hM) = h.classify t (Φ t M) (hcut t M hM))

include hφ in

theorem mk_pullbackAlong_postComp_of_transform {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver s D'.toBase) :
    (Quotient.mk _ (h.poincare.pullbackAlong (postComp φ x)) : RigidifiedLineBundle.Classes c ε s) =
      Quotient.mk _ (Φ s (h'.poincare.pullbackAlong x)) := by
  have hm : P'.P s (h'.poincare.pullbackAlong x) :=
    P'.toSubPicCondition.pullback_mem _ _ x _ h'.poincare_mem
  have hx : x = h'.classify s (h'.poincare.pullbackAlong x) hm := h'.classify_unique s _ _ x ⟨Iso.refl _⟩
  have key := hφ s (h'.poincare.pullbackAlong x) hm
  rw [← hx] at key
  rw [key]
  exact Quotient.sound (h.classify_spec s _ _)

include hφ in

theorem mk_transform_eq_of_nonempty_iso {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c' ε' s) (hM : P'.P s M) (hM' : P'.P s M') (e : Nonempty (M.L ≅ M'.L)) :
    (Quotient.mk _ (Φ s M) : RigidifiedLineBundle.Classes c ε s) = Quotient.mk _ (Φ s M') := by
  have hcl : h'.classify s M hM = h'.classify s M' hM' :=
    h'.classify_unique s M' hM' _ ⟨(h'.classify_spec s M hM).some ≪≫ e.some⟩
  have h3 : h.classify s (Φ s M) (hcut s M hM) = h.classify s (Φ s M') (hcut s M' hM') := by
    rw [← hφ s M hM, ← hφ s M' hM', hcl]
  have i1 := h.classify_spec s (Φ s M) (hcut s M hM)
  have i2 := h.classify_spec s (Φ s M') (hcut s M' hM')
  rw [h3] at i1
  exact Quotient.sound ⟨i1.some.symm ≪≫ i2.some⟩

theorem representableBy_homEquiv_schemeHomOverToOverHom_coe {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver s D.toBase) :
    (h.representableBy.homEquiv (X := Over.mk s) (schemeHomOverToOverHom x)).1 =
      Quotient.mk _ (h.poincare.pullbackAlong x) := rfl

include hφ in

theorem schemeHomOverComp_mul_of_transform
    (htensor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c' ε' t),
      Nonempty ((Φ t (M.tensor M')).L ≅ ((Φ t M).tensor (Φ t M')).L))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D'.toBase) :
    NeronModelInfra.schemeHomOverComp (h'.relativeGroupLaw.mul s x y) φ =
      h.relativeGroupLaw.mul s (NeronModelInfra.schemeHomOverComp x φ)
        (NeronModelInfra.schemeHomOverComp y φ) := by
  letI := h.grpObj
  letI := h'.grpObj
  letI := P.commGroupObj (Opposite.op (Over.mk s))
  letI := P'.commGroupObj (Opposite.op (Over.mk s))

  have eL : (Quotient.mk _ (h.poincare.pullbackAlong
        (NeronModelInfra.schemeHomOverComp (h'.relativeGroupLaw.mul s x y) φ)) :
        RigidifiedLineBundle.Classes c ε s) =
      Quotient.mk _ ((Φ s (h'.poincare.pullbackAlong x)).tensor (Φ s (h'.poincare.pullbackAlong y))) := by

    change (Quotient.mk _ (h.poincare.pullbackAlong (postComp φ (h'.relativeGroupLaw.mul s x y))) :
        RigidifiedLineBundle.Classes c ε s) = _
    rw [mk_pullbackAlong_postComp_of_transform h h' Φ hcut φ hφ]

    have hxy : (Quotient.mk _ (h'.poincare.pullbackAlong (h'.relativeGroupLaw.mul s x y)) :
          RigidifiedLineBundle.Classes c' ε' s) =
        Quotient.mk _ ((h'.poincare.pullbackAlong x).tensor (h'.poincare.pullbackAlong y)) := by
      have hm := congrArg Subtype.val
        (h'.homEquiv_mul (Over.mk s) (schemeHomOverToOverHom x) (schemeHomOverToOverHom y))
      exact hm
    have exy : Nonempty ((h'.poincare.pullbackAlong (h'.relativeGroupLaw.mul s x y)).L ≅
        ((h'.poincare.pullbackAlong x).tensor (h'.poincare.pullbackAlong y)).L) := Quotient.exact hxy
    rw [mk_transform_eq_of_nonempty_iso h h' Φ hcut φ hφ s _ _
      (P'.toSubPicCondition.pullback_mem _ _ _ _ h'.poincare_mem)
      (P'.tensor_mem _ _ _ (P'.toSubPicCondition.pullback_mem _ _ x _ h'.poincare_mem)
        (P'.toSubPicCondition.pullback_mem _ _ y _ h'.poincare_mem)) exy]
    exact Quotient.sound (htensor s _ _)

  have eR : (Quotient.mk _ (h.poincare.pullbackAlong
        (h.relativeGroupLaw.mul s (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ))) : RigidifiedLineBundle.Classes c ε s) =
      Quotient.mk _ ((Φ s (h'.poincare.pullbackAlong x)).tensor (Φ s (h'.poincare.pullbackAlong y))) := by
    have hm := congrArg Subtype.val
      (h.homEquiv_mul (Over.mk s) (schemeHomOverToOverHom (NeronModelInfra.schemeHomOverComp x φ))
        (schemeHomOverToOverHom (NeronModelInfra.schemeHomOverComp y φ)))
    refine hm.trans ?_
    change Quotient.map₂ (fun L M => L.tensor M) (fun _ _ hL _ _ hM => RigidifiedLineBundle.tensor_congr hL hM)
        (Quotient.mk _ (h.poincare.pullbackAlong (postComp φ x)))
        (Quotient.mk _ (h.poincare.pullbackAlong (postComp φ y))) = _
    rw [mk_pullbackAlong_postComp_of_transform h h' Φ hcut φ hφ s x,
      mk_pullbackAlong_postComp_of_transform h h' Φ hcut φ hφ s y]
    rfl
  exact h.ext_of_iso s _ _ (Quotient.exact (eL.trans eR.symm))

include hφ in

theorem zeroSection_comp_of_transform
    (hunit : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      Nonempty ((Φ t (RigidifiedLineBundle.unit t)).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L)) :
    D'.zeroSection ≫ φ.1 = D.zeroSection := by
  suffices hcls : (Quotient.mk _ (h.poincare.pullbackAlong (postComp φ ⟨D'.zeroSection, D'.zeroSection_toBase⟩)) :
        RigidifiedLineBundle.Classes c ε (𝟙 _)) =
      Quotient.mk _ (h.poincare.pullbackAlong ⟨D.zeroSection, D.zeroSection_toBase⟩) by
    exact congrArg Subtype.val (h.ext_of_iso (𝟙 _)
      (postComp φ ⟨D'.zeroSection, D'.zeroSection_toBase⟩) ⟨D.zeroSection, D.zeroSection_toBase⟩ (Quotient.exact hcls))
  rw [mk_pullbackAlong_postComp_of_transform h h' Φ hcut φ hφ]
  have hz : (Quotient.mk _ (Φ (𝟙 _) (h'.poincare.pullbackAlong ⟨D'.zeroSection, D'.zeroSection_toBase⟩)) :
        RigidifiedLineBundle.Classes c ε (𝟙 _)) =
      Quotient.mk _ (Φ (𝟙 _) (RigidifiedLineBundle.unit (c := c') (ε := ε') (𝟙 _))) :=
    mk_transform_eq_of_nonempty_iso h h' Φ hcut φ hφ (𝟙 _) _ _
      (P'.toSubPicCondition.pullback_mem _ _ _ _ h'.poincare_mem) (P'.toSubPicCondition.unit_mem _) h'.zero
  rw [hz]
  exact Quotient.sound ⟨(hunit (𝟙 _)).some ≪≫ h.zero.some.symm⟩

end AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open _root_.AlgebraicGeometry.RelPicard _root_.P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform.AlgebraicGeometry.RelPicard in
theorem solution
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {P : SubPicGroupCondition c ε} {P' : SubPicGroupCondition c' ε'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    (h' : RepresentsRelSubPic c' ε' P'.toSubPicCondition D')
    (Φ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      RigidifiedLineBundle c' ε' t → RigidifiedLineBundle c ε t)
    (hcut : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t),
      P'.P t M → P.P t (Φ t M))
    (htensor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c' ε' t),
      Nonempty ((Φ t (M.tensor M')).L ≅ ((Φ t M).tensor (Φ t M')).L))
    (hunit : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      Nonempty ((Φ t (RigidifiedLineBundle.unit t)).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L))
    (φ : SchemeHomOver D'.toBase D.toBase)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
        (hM : P'.P t M),
        postComp φ (h'.classify t M hM) = h.classify t (Φ t M) (hcut t M hM)) :
    (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D'.toBase),
      NeronModelInfra.schemeHomOverComp (h'.relativeGroupLaw.mul s x y) φ =
        h.relativeGroupLaw.mul s (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ)) ∧
    D'.zeroSection ≫ φ.1 = D.zeroSection :=
  ⟨fun s x y => RepresentsRelSubPic.schemeHomOverComp_mul_of_transform h h' Φ hcut φ hφ htensor s x y,
    RepresentsRelSubPic.zeroSection_comp_of_transform h h' Φ hcut φ hφ hunit⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform (solution)
