-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_representsRelSubPic_of_finite_etale_descent_of_bijective_sections_of_forall_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d6f2b48b-4548-5640-b20b-f652fd1515cd

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_DescentAction
import Theorems.Thm_AlgebraicGeometry_RelPicard_isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections
import Theorems.Thm_AlgebraicGeometry_exists_representableBy_of_representableBy_restrict_finiteEtale_of_forall_orbit
import Theorems.Thm_AlgebraicGeometry_smooth_isSeparated_quasiCompact_geometricallyConnected_of_finiteEtale_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_of_finite_etale_descent_of_bijective_sections_of_forall_orbit
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian Opposite

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Algebra.Etale R R']
    [Module.FaithfullyFlat R R']
    (D' : RelativePic0Designation R' (SmoothProperCurve.baseChange R c R'))
    (h' : RepresentsRelSubPic (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
      (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)) D')
    (hsm : Smooth D'.toBase) (hsep : IsSeparated D'.toBase) (hqc : QuasiCompact D'.toBase)
    (hgc : GeometricallyConnected D'.toBase)
    (haff : ∀ x : D'.P, ∃ W : D'.P.Opens, IsAffineOpen W ∧
      ∀ r : ↑(pullback (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R')),
        (pullback.fst (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R')) r = x →
        (DescentAction.ofRepresentableBy (SmoothProperCurve.specMap R R')
          (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
          (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).act r ∈ W) :
    ∃ D : RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsSeparated D.toBase ∧ QuasiCompact D.toBase ∧ GeometricallyConnected D.toBase ∧
        ∃ e : pullback D.toBase (SmoothProperCurve.specMap R R') ≅ D'.P,
          e.hom ≫ D'.toBase = pullback.snd D.toBase (SmoothProperCurve.specMap R R') := by

  obtain ⟨X, f, rep, e, he⟩ := AlgebraicGeometry.exists_representableBy_of_representableBy_restrict_finiteEtale_of_forall_orbit
    R R' (relSubPicPresheaf c ε (algEquivZeroCut c ε))
    (AlgebraicGeometry.RelPicard.isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections
      R c ε hH0 R')
    D'.toBase (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h') haff

  obtain ⟨hs, hp, hq, hg⟩ :=
    AlgebraicGeometry.smooth_isSeparated_quasiCompact_geometricallyConnected_of_finiteEtale_baseChange R R' f D'.toBase
      hsm hsep hqc hgc e he

  let u₀ : (relSubPicPresheaf c ε (algEquivZeroCut c ε)).obj (op (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :=
    ⟨relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)), (algEquivZeroCut c ε).unit_mem (𝟙 _)⟩
  let z : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk f := rep.homEquiv.symm u₀
  let D : RelativePic0Designation R c :=
    { P := X, toBase := f, zeroSection := z.left, zeroSection_toBase := Over.w z }
  have hz : (Over.homMk D.zeroSection D.zeroSection_toBase :
      Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk D.toBase) = z := Over.OverMorphism.ext rfl
  have h0 : (rep.homEquiv (Over.homMk D.zeroSection D.zeroSection_toBase :
      Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk D.toBase)).1 =
      relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)) := by
    rw [hz]
    change (rep.homEquiv (rep.homEquiv.symm u₀)).1 = _
    rw [Equiv.apply_symm_apply]
  exact ⟨D, RepresentsRelSubPic.nonempty_of_representableBy rep h0, hs, hp, hq, hg, e, he⟩

end S_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_of_finite_etale_descent_of_bijective_sections_of_forall_orbit
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_of_finite_etale_descent_of_bijective_sections_of_forall_orbit (solution)
