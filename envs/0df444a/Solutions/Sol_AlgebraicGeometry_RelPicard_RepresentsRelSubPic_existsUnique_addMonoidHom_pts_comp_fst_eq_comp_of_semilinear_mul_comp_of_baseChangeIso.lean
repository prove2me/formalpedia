-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_addMonoidHom_pts_comp_fst_eq_comp_of_semilinear_mul_comp_of_baseChangeIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d081fa52-730c-5057-aee0-9bd9697d1d92

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_addMonoidHom_pts_comp_fst_eq_comp_of_semilinear_mul_comp_of_baseChangeIso

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve"

universe u

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (hR : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hPR : Nonempty (hR.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (J : Type u) [AddCommGroup J]
    (pts : J ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (D.baseChange R').toBase)
    (hadd : ∀ a b : J, Nonempty
      ((hR.poincare.pullbackAlong (pts (a + b))).L ≅
        (hR.poincare.pullbackAlong (pts a)).L ⊗ (hR.poincare.pullbackAlong (pts b)).L))
    (σ : R →+* R) (hσ : (algebraMap R R').comp σ = algebraMap R R')
    (χ : SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom σ)) D.toBase)
    (hχmul : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y).1 ≫ χ.1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (s ≫ Spec.map (CommRingCat.ofHom σ))
          ⟨x.1 ≫ χ.1, by rw [Category.assoc, χ.2, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ χ.1, by rw [Category.assoc, χ.2, ← Category.assoc, y.2]⟩).1) :
    ∃! e : J →+ J, ∀ y : J,
      (pts (e y)).1 ≫ pullback.fst D.toBase (specMap R R') = ((pts y).1 ≫ pullback.fst D.toBase (specMap R R')) ≫ χ.1 := by
  classical
  let fstD : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  let Q : J → SchemeHomOver (𝟙 (Spec (CommRingCat.of R')) ≫ specMap R R') D.toBase :=
    fun y => postComp fstD (BaseChange.overR R' (pts y))

  have hT1 : ∀ w : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (D.baseChange R').toBase,
      Nonempty ((BaseChange.toR c ε R' (hR.poincare.pullbackAlong w)).L ≅
        (h.poincare.pullbackAlong (postComp fstD (BaseChange.overR R' w))).L) := by
    intro w
    obtain ⟨ePR⟩ := hPR
    exact ⟨(BaseChange.toR_pullbackAlong_iso c ε R' w hR.poincare).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c (BaseChange.overR R' w))).mapIso
        ((Scheme.Modules.pullback (BaseChange.κ c R' (D.baseChange R').toBase).inv).mapIso ePR ≪≫
          BaseChange.toR_ofR_iso c ε R' _) ≪≫
      RigidifiedLineBundle.pullbackAlongPullbackAlongIso' h.poincare fstD (BaseChange.overR R' w)⟩
  have hQadd : ∀ a b : J, Q (a + b) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (Q a) (Q b) := by
    intro a b
    apply h.ext_of_iso
    obtain ⟨e1⟩ := hT1 (pts (a + b))
    obtain ⟨ea⟩ := hT1 (pts a)
    obtain ⟨eb⟩ := hT1 (pts b)
    obtain ⟨eab⟩ := hadd a b
    obtain ⟨emul⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut c ε) h
      (T := Over.mk (𝟙 (Spec (CommRingCat.of R')) ≫ specMap R R'))
      (schemeHomOverToOverHom (Q a)) (schemeHomOverToOverHom (Q b))
    exact ⟨e1.symm ≪≫
      (Scheme.Modules.pullback (BaseChange.κ c R' (𝟙 (Spec (CommRingCat.of R')))).inv).mapIso eab ≪≫
      Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (ea ⊗ᵢ eb) ≪≫ emul.symm⟩

  have hbase0 : specMap R R' ≫ Spec.map (CommRingCat.ofHom σ) = specMap R R' := by
    show Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ _ = _
    rw [← Spec.map_comp]
    show Spec.map (CommRingCat.ofHom ((algebraMap R R').comp σ)) = _
    rw [hσ]
  have hbase : (𝟙 (Spec (CommRingCat.of R')) ≫ specMap R R') ≫ Spec.map (CommRingCat.ofHom σ) =
      𝟙 (Spec (CommRingCat.of R')) ≫ specMap R R' := by
    rw [Category.assoc, hbase0]

  have hmulbase : ∀ {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (e : t = t')
      (x y : SchemeHomOver t D.toBase) (x' y' : SchemeHomOver t' D.toBase), x'.1 = x.1 → y'.1 = y.1 →
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t x y).1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t' x' y').1 := by
    intro T t t' e x y x' y' hx hy
    subst e
    obtain rfl : x' = x := Subtype.ext hx
    obtain rfl : y' = y := Subtype.ext hy
    rfl

  have hq : ∀ y : J, ((pts y).1 ≫ pullback.fst D.toBase (specMap R R') ≫ χ.1) ≫ D.toBase =
      𝟙 _ ≫ specMap R R' := by
    intro y
    rw [Category.assoc, Category.assoc, χ.2, ← Category.assoc (pullback.fst _ _), pullback.condition,
      Category.assoc, hbase0, ← Category.assoc]
    congr 1
    exact (pts y).2
  let lift : J → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (D.baseChange R').toBase := fun y =>
    ⟨pullback.lift ((pts y).1 ≫ pullback.fst D.toBase (specMap R R') ≫ χ.1) (𝟙 _) (hq y),
      show _ ≫ pullback.snd _ _ = _ from pullback.lift_snd _ _ _⟩
  let e₀ : J → J := fun y => pts.symm (lift y)
  have hread : ∀ y : J, (pts (e₀ y)).1 ≫ pullback.fst D.toBase (specMap R R') =
      ((pts y).1 ≫ pullback.fst D.toBase (specMap R R')) ≫ χ.1 := by
    intro y
    show (pts (pts.symm (lift y))).1 ≫ _ = _
    rw [Equiv.apply_symm_apply, Category.assoc]
    exact pullback.lift_fst _ _ _
  have hQinj : ∀ y y' : J, (Q y).1 = (Q y').1 → y = y' := by
    intro y y' hQ
    apply pts.injective
    apply Subtype.ext
    apply pullback.hom_ext
    · exact hQ
    · show (pts y).1 ≫ (D.baseChange R').toBase = (pts y').1 ≫ (D.baseChange R').toBase
      rw [(pts y).2, (pts y').2]
  have hadd' : ∀ a b : J, e₀ (a + b) = e₀ a + e₀ b := by
    intro a b
    apply hQinj
    have step1 : (Q (e₀ (a + b))).1 = (Q (a + b)).1 ≫ χ.1 := hread (a + b)
    have step2 : (Q (a + b)).1 ≫ χ.1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul
          ((𝟙 (Spec (CommRingCat.of R')) ≫ specMap R R') ≫ Spec.map (CommRingCat.ofHom σ))
          ⟨(Q a).1 ≫ χ.1, by rw [Category.assoc, χ.2, ← Category.assoc, (Q a).2]⟩
          ⟨(Q b).1 ≫ χ.1, by rw [Category.assoc, χ.2, ← Category.assoc, (Q b).2]⟩).1 := by
      rw [hQadd a b]
      exact hχmul _ (Q a) (Q b)
    rw [step1, step2, hQadd (e₀ a) (e₀ b)]
    exact hmulbase hbase _ _ (Q (e₀ a)) (Q (e₀ b)) (hread a) (hread b)
  refine ⟨AddMonoidHom.mk' e₀ hadd', hread, ?_⟩
  intro e' he'
  ext y
  apply pts.injective
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [he' y]
    exact (hread y).symm
  · show (pts (e' y)).1 ≫ (D.baseChange R').toBase = (pts (e₀ y)).1 ≫ (D.baseChange R').toBase
    rw [(pts (e' y)).2, (pts (e₀ y)).2]

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_addMonoidHom_pts_comp_fst_eq_comp_of_semilinear_mul_comp_of_baseChangeIso
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_addMonoidHom_pts_comp_fst_eq_comp_of_semilinear_mul_comp_of_baseChangeIso (solution)
