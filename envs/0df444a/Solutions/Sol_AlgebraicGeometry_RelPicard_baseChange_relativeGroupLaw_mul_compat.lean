-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/11fd54d3-c84f-5a84-a7c8-ca4ee88f9901

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard.BaseChange"

open scoped CategoryTheory.MonObj

namespace GrpBCLawSol

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

noncomputable def pullbackAlongComp {T T' T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (φ : SchemeHomOver t' t) (ψ : SchemeHomOver t'' t') :
    ((M.pullbackAlong φ).pullbackAlong ψ).L ≅ (M.pullbackAlong (postComp φ ψ)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) (baseChangeSnd c φ)).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c φ ψ)).app M.L

noncomputable def pullbackAlongCongr {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) {φ ψ : SchemeHomOver t' t}
    (e : φ.1 = ψ.1) : (M.pullbackAlong φ).L ≅ (M.pullbackAlong ψ).L :=
  eqToIso (by cases φ; cases ψ; cases e; rfl)

end GrpBCLawSol

open GrpBCLawSol in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (x y : SchemeHomOver t' (D.baseChange R').toBase)
    (x₁ y₁ : SchemeHomOver (t' ≫ specMap R R') D.toBase)
    (hx : x₁.1 = x.1 ≫ pullback.fst D.toBase (specMap R R'))
    (hy : y₁.1 = y.1 ≫ pullback.fst D.toBase (specMap R R')) :
    ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').mul t' x y).1 ≫
        pullback.fst D.toBase (specMap R R') =
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (t' ≫ specMap R R') x₁ y₁).1 := by
  classical

  let hg : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D := h
  let hg' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)).toSubPicCondition (D.baseChange R') := h'
  letI := hg'.grpObj
  letI := hg.grpObj

  let ψ₀ : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  let Θ : SchemeHomOver t' (D.baseChange R').toBase → SchemeHomOver (t' ≫ specMap R R') D.toBase :=
    fun z => postComp ψ₀ (overR R' z)
  have hΘ : ∀ z, (Θ z).1 = z.1 ≫ pullback.fst D.toBase (specMap R R') := fun z => rfl

  obtain rfl : x₁ = Θ x := Subtype.ext (hx.trans (hΘ x).symm)
  obtain rfl : y₁ = Θ y := Subtype.ext (hy.trans (hΘ y).symm)

  let P' : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) (D.baseChange R').toBase :=
    ofR c ε R' (h.poincare.pullbackAlong ψ₀)
  have chain : ∀ (z : SchemeHomOver t' (D.baseChange R').toBase),
      (toR c ε R' (P'.pullbackAlong z)).L ≅ (h.poincare.pullbackAlong (Θ z)).L :=
    fun z => (toR_pullbackAlong_iso c ε R' z P').symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c (overR R' z))).mapIso (toR_ofR_iso c ε R' _) ≪≫
      pullbackAlongComp h.poincare ψ₀ (overR R' z)

  have poinc : ∀ z : SchemeHomOver t' (D.baseChange R').toBase,
      (toR c ε R' (h'.poincare.pullbackAlong z)).L ≅ (h.poincare.pullbackAlong (Θ z)).L :=
    fun z =>
      (Scheme.Modules.pullback (κ c R' t').inv).mapIso
          ((Scheme.Modules.pullback (baseChangeSnd (baseChange R c R') z)).mapIso hP.some) ≪≫
        chain z

  let a : Over.mk t' ⟶ Over.mk (D.baseChange R').toBase := schemeHomOverToOverHom x
  let b : Over.mk t' ⟶ Over.mk (D.baseChange R').toBase := schemeHomOverToOverHom y
  obtain ⟨i₂⟩ := hg'.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk t') a b
  obtain ⟨i₁⟩ := hg.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk (t' ≫ specMap R R'))
    (schemeHomOverToOverHom (Θ x)) (schemeHomOverToOverHom (Θ y))

  suffices key : Θ (hg'.relativeGroupLaw.mul t' x y) = hg.relativeGroupLaw.mul (t' ≫ specMap R R') (Θ x) (Θ y) by
    exact (hΘ _).symm.trans (congrArg Subtype.val key)
  refine hg.ext_of_iso (t' ≫ specMap R R') _ _ ⟨?_⟩
  exact (poinc (hg'.relativeGroupLaw.mul t' x y)).symm ≪≫
    (Scheme.Modules.pullback (κ c R' t').inv).mapIso i₂ ≪≫
    Scheme.Modules.pullbackTensorObjIso (κ c R' t').inv _ _ ≪≫
    (poinc x ⊗ᵢ poinc y) ≪≫ i₁.symm

end S_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat (solution)
