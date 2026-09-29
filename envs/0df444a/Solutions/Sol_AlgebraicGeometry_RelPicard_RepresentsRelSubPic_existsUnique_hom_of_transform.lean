-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_hom_of_transform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b9c6504b-05f3-5429-ac0a-0e4895a10c17

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

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform.AlgebraicGeometry.RelPicard"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Scheme Scheme.Modules RelPicard.RepresentsRelSubPic"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "postComp RigidifiedLineBundle SubPicCondition RepresentsRelSubPic"
namespace RepresentsRelSubPic
p2m_export "AlgebraicGeometry.RelPicard.RepresentsRelSubPic" "classify classify_spec classify_unique poincare poincare_mem"
p2m_open "AlgebraicGeometry.RelPicard.RepresentsRelSubPic AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {P : SubPicCondition c ε} {P' : SubPicCondition c' ε'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε P D) (h' : RepresentsRelSubPic c' ε' P' D')
    (Φ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      RigidifiedLineBundle c' ε' t → RigidifiedLineBundle c ε t)
    (hcut : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t),
      P'.P t M → P.P t (Φ t M))

noncomputable def transformHom : SchemeHomOver D'.toBase D.toBase :=
  h.classify D'.toBase (Φ D'.toBase h'.poincare) (hcut _ _ h'.poincare_mem)

variable
    (hcongr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c' ε' t),
      Nonempty (M.L ≅ M'.L) → Nonempty ((Φ t M).L ≅ (Φ t M').L))
    (hnat : ∀ {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
      (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c' ε' t),
      Nonempty (((Φ t M).pullbackAlong ψ).L ≅ (Φ t' (M.pullbackAlong ψ)).L))

include hcongr hnat in

theorem postComp_transformHom_classify {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c' ε' t) (hM : P'.P t M) :
    postComp (transformHom h h' Φ hcut) (h'.classify t M hM) = h.classify t (Φ t M) (hcut t M hM) := by
  refine h.classify_unique t _ _ _ ⟨?_⟩
  exact (h.poincare.pullbackAlongPullbackAlongIso _ _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (h.classify_spec D'.toBase _ _).some ≪≫
    (hnat (h'.classify t M hM) h'.poincare).some ≪≫
    (hcongr t _ _ (h'.classify_spec t M hM)).some

theorem transformHom_unique (g : SchemeHomOver D'.toBase D.toBase)
    (hg : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
      (hM : P'.P t M), postComp g (h'.classify t M hM) = h.classify t (Φ t M) (hcut t M hM)) :
    g = transformHom h h' Φ hcut := by
  have hid : h'.classify D'.toBase h'.poincare h'.poincare_mem = ⟨𝟙 _, Category.id_comp _⟩ :=
    (h'.classify_unique D'.toBase _ _ _ ⟨h'.poincare.pullbackAlongIdIso⟩).symm
  have key := hg D'.toBase h'.poincare h'.poincare_mem
  rw [hid] at key
  refine Eq.trans ?_ key
  apply Subtype.ext
  simp [postComp]

include hcongr hnat in

theorem existsUnique_hom_of_transform' :
    ∃! φ : SchemeHomOver D'.toBase D.toBase,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
        (hM : P'.P t M),
        postComp φ (h'.classify t M hM) = h.classify t (Φ t M) (hcut t M hM) :=
  ⟨transformHom h h' Φ hcut, fun t M hM => postComp_transformHom_classify h h' Φ hcut hcongr hnat t M hM,
    fun g hg => transformHom_unique h h' Φ hcut g hg⟩

end AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open _root_.AlgebraicGeometry.RelPicard _root_.P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform.AlgebraicGeometry.RelPicard in
theorem solution
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {P : SubPicCondition c ε} {P' : SubPicCondition c' ε'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε P D) (h' : RepresentsRelSubPic c' ε' P' D')
    (Φ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      RigidifiedLineBundle c' ε' t → RigidifiedLineBundle c ε t)
    (hcongr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c' ε' t),
      Nonempty (M.L ≅ M'.L) → Nonempty ((Φ t M).L ≅ (Φ t M').L))
    (hnat : ∀ {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
      (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c' ε' t),
      Nonempty (((Φ t M).pullbackAlong ψ).L ≅ (Φ t' (M.pullbackAlong ψ)).L))
    (hcut : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t),
      P'.P t M → P.P t (Φ t M)) :
    ∃! φ : SchemeHomOver D'.toBase D.toBase,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
        (hM : P'.P t M),
        postComp φ (h'.classify t M hM) = h.classify t (Φ t M) (hcut t M hM) :=
  RepresentsRelSubPic.existsUnique_hom_of_transform' h h' Φ hcut hcongr hnat

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform (solution)
