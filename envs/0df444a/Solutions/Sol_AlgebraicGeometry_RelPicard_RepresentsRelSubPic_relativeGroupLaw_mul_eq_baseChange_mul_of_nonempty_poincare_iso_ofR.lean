-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8a744305-fe28-5384-8d86-d5d829d36ada

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian"

p2m_open "CategoryTheory.MonoidalCategory"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp RelPicard.BaseChange.κ Scheme.Modules.pullbackTensorObjIso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd postComp baseChangeSnd_comp RigidifiedLineBundle RepresentsRelSubPic algEquivZeroCut BaseChange.κ BaseChange.ofR algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso"
namespace BaseChange
p2m_export "AlgebraicGeometry.RelPicard.BaseChange" "κ overR baseChangeSnd_κ_hom toR ofR toR_ofR_iso"
p2m_open "AlgebraicGeometry.RelPicard.BaseChange AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (R' : Type u) [CommRing R'] [Algebra R R']

noncomputable def LAW_ofR_pullbackAlong_iso {T T'' : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    {t'' : T'' ⟶ Spec (CommRingCat.of R')} (ψ : SchemeHomOver t'' t')
    (X : RigidifiedLineBundle c ε (t' ≫ specMap R R')) :
    ((ofR c ε R' X).pullbackAlong ψ).L ≅ (ofR c ε R' (X.pullbackAlong (overR R' ψ))).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd (baseChange R c R') ψ) (κ c R' t').hom).app X.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_κ_hom c R' ψ)).app X.L ≪≫
    ((Scheme.Modules.pullbackComp (κ c R' t'').hom (baseChangeSnd c (overR R' ψ))).app X.L).symm

omit [Algebra R R'] in

noncomputable def LAW_pullbackAlong_pullbackAlong_iso {X₀ X₁ X₂ : Scheme.{u}} {x₀ : X₀ ⟶ Spec (CommRingCat.of R)}
    {x₁ : X₁ ⟶ Spec (CommRingCat.of R)} {x₂ : X₂ ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε x₀) (φ : SchemeHomOver x₁ x₀) (ψ : SchemeHomOver x₂ x₁) :
    ((M.pullbackAlong φ).pullbackAlong ψ).L ≅ (M.pullbackAlong (postComp φ ψ)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) (baseChangeSnd c φ)).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c φ ψ)).app M.L

noncomputable def LAW_transportIso {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (e : h'.poincare.L ≅ (BaseChange.ofR c ε R'
        (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')} (z : SchemeHomOver t' (D.baseChange R').toBase) :
    (toR c ε R' (h'.poincare.pullbackAlong z)).L ≅
      (h.poincare.pullbackAlong (RelativeGroupLaw.baseChangePointToBase (specMap R R') z)).L :=
  ((Scheme.Modules.pullback (κ c R' t').inv).mapIso
      ((Scheme.Modules.pullback (baseChangeSnd (baseChange R c R') z)).mapIso e ≪≫ LAW_ofR_pullbackAlong_iso c ε R' z _) ≪≫
    toR_ofR_iso c ε R' _ ≪≫
    LAW_pullbackAlong_pullbackAlong_iso c ε h.poincare _ _ : _)

end AlgebraicGeometry.RelPicard.BaseChange

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
        (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L)) :
    ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' (D.baseChange R').toBase),
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').mul t' x y =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).baseChange (specMap R R')).mul t' x y := by
  intro T t' x y
  obtain ⟨e⟩ := hP
  rw [RelativeGroupLaw.baseChange_mul]
  apply (RelativeGroupLaw.baseChangePointEquiv (specMap R R') t').injective
  show RelativeGroupLaw.baseChangePointToBase (specMap R R') _ = RelativeGroupLaw.baseChangePointToBase (specMap R R') _
  rw [RelativeGroupLaw.baseChangePointToBase_ofBase]
  apply h.ext_of_iso (t' ≫ specMap R R')

  obtain ⟨m'⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso
    (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h'
    (T := Over.mk t') (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
  obtain ⟨m⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut c ε) h
    (T := Over.mk (t' ≫ specMap R R'))
    (schemeHomOverToOverHom (RelativeGroupLaw.baseChangePointToBase (specMap R R') x))
    (schemeHomOverToOverHom (RelativeGroupLaw.baseChangePointToBase (specMap R R') y))
  exact ⟨(AlgebraicGeometry.RelPicard.BaseChange.LAW_transportIso c ε R' h h' e _).symm ≪≫
    (Scheme.Modules.pullback (AlgebraicGeometry.RelPicard.BaseChange.κ c R' t').inv).mapIso m' ≪≫
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    (AlgebraicGeometry.RelPicard.BaseChange.LAW_transportIso c ε R' h h' e x ⊗ᵢ
      AlgebraicGeometry.RelPicard.BaseChange.LAW_transportIso c ε R' h h' e y) ≪≫ m.symm⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR (solution)
