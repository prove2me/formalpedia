-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e5f683f6-ac54-5259-9523-818c71dbc6c6

import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra Opposite

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
    (T : Over (Spec (CommRingCat.of R))) :
    Presieve.IsSheafFor (relSubPicPresheaf c ε (algEquivZeroCut c ε))
      (Presieve.singleton ((Over.mapPullbackAdj (SmoothProperCurve.specMap R R')).counit.app T)) := by
  classical
  rw [Presieve.isSheafFor_singleton]
  rintro ⟨ξ, hξ⟩ hx

  have hπ : ((Over.mapPullbackAdj (specMap R R')).counit.app T).left = pullback.fst T.hom (specMap R R') := by
    simp
  let πS : SchemeHomOver (pullback.snd T.hom (specMap R R') ≫ specMap R R') T.hom :=
    ⟨pullback.fst T.hom (specMap R R'), pullback.condition⟩

  set M' : RigidifiedLineBundle c ε (pullback.snd T.hom (specMap R R') ≫ specMap R R') := ξ.out with hM'def
  have hM' : Quotient.mk _ M' = ξ := Quotient.out_eq ξ
  have hξP : FibrewiseAlgEquivZero M' := by
    have h : (algEquivZeroCut c ε).onClasses _ ξ := hξ
    rw [← hM'] at h
    exact h

  have hcompat : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
      (p₁ p₂ : SchemeHomOver z (pullback.snd T.hom (specMap R R') ≫ specMap R R')),
      p₁.1 ≫ pullback.fst T.hom (specMap R R') = p₂.1 ≫ pullback.fst T.hom (specMap R R') →
        Nonempty ((M'.pullbackAlong p₁).L ≅ (M'.pullbackAlong p₂).L) := by
    intro Z z p₁ p₂ hp
    let P₁ : Over.mk z ⟶ (Over.map (specMap R R')).obj ((Over.pullback (specMap R R')).obj T) :=
      Over.homMk p₁.1 p₁.2
    let P₂ : Over.mk z ⟶ (Over.map (specMap R R')).obj ((Over.pullback (specMap R R')).obj T) :=
      Over.homMk p₂.1 p₂.2
    have hP : P₁ ≫ (Over.mapPullbackAdj (specMap R R')).counit.app T =
        P₂ ≫ (Over.mapPullbackAdj (specMap R R')).counit.app T := by
      ext
      change p₁.1 ≫ ((Over.mapPullbackAdj (specMap R R')).counit.app T).left =
        p₂.1 ≫ ((Over.mapPullbackAdj (specMap R R')).counit.app T).left
      rw [hπ]
      exact hp
    have h := congrArg Subtype.val (hx P₁ P₂ hP)
    rw [relSubPicPresheaf_map_coe, relSubPicPresheaf_map_coe] at h
    change RigidifiedLineBundle.classesMap _ ξ = RigidifiedLineBundle.classesMap _ ξ at h
    rw [← hM'] at h
    exact Quotient.exact h

  obtain ⟨M, ⟨e⟩⟩ :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_descent_finite_faithfullyFlat_of_bijective_sections
      R c ε hH0 R' T.hom M' hcompat

  have hM : FibrewiseAlgEquivZero M :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat
      R c ε R' T.hom M ((algEquivZeroCut c ε).congr _ M' (M.pullbackAlong πS) ⟨e.symm⟩ hξP)

  have hmap : ∀ (ψ : SchemeHomOver (pullback.snd T.hom (specMap R R') ≫ specMap R R') T.hom),
      ψ.1 = pullback.fst T.hom (specMap R R') → ∀ N : RigidifiedLineBundle c ε T.hom,
        RigidifiedLineBundle.classesMap ψ (Quotient.mk _ N) = Quotient.mk _ (N.pullbackAlong πS) := by
    rintro ⟨ψ₁, hψ⟩ h N
    change ψ₁ = _ at h
    subst h
    rfl
  refine ⟨⟨Quotient.mk _ M, show (algEquivZeroCut c ε).onClasses T.hom (Quotient.mk _ M) from
    (SubPicCondition.onClasses_mk (algEquivZeroCut c ε) T.hom M).2 hM⟩, ?_, ?_⟩
  ·
    apply Subtype.ext
    rw [relSubPicPresheaf_map_coe]
    change RigidifiedLineBundle.classesMap _ (Quotient.mk _ M) = ξ
    rw [← hM']
    exact (hmap _ hπ M).trans (Quotient.sound ⟨e⟩)
  ·
    rintro ⟨ξ₁, hξ₁⟩ hy
    apply Subtype.ext
    change ξ₁ = Quotient.mk _ M
    obtain ⟨N, rfl⟩ := Quotient.exists_rep ξ₁
    have h₁ := congrArg Subtype.val hy
    rw [relSubPicPresheaf_map_coe] at h₁
    change RigidifiedLineBundle.classesMap _ (Quotient.mk _ N) = ξ at h₁
    have h₃ : Quotient.mk _ (N.pullbackAlong πS) = Quotient.mk _ M' :=
      ((hmap _ hπ N).symm.trans h₁).trans hM'.symm
    have h₂ : Nonempty ((N.pullbackAlong πS).L ≅ (M.pullbackAlong πS).L) :=
      ⟨(Quotient.exact h₃).some ≪≫ e.symm⟩
    exact Quotient.sound
      (AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
        R c ε hH0 R' T.hom N M h₂)

end S_AlgebraicGeometry_RelPicard_isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections (solution)
