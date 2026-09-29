-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_nonempty_pullback_iso_tensorUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/6fa7dc6a-a7e6-5a63-9aee-aff6b3c858b8

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
import Theorems.Thm_Algebra_exists_isDirectLimit_of_finitePresentation
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field_monoidalV2
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_nonempty_pullback_iso_tensorUnit
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

noncomputable section

namespace PicInj

def Triv {A Y : Scheme.{0}} (𝓜 : A.Modules) (p : Y ⟶ A) : Prop :=
  Nonempty ((Scheme.Modules.pullback p).obj 𝓜 ≅ 𝟙_ Y.Modules)

theorem Triv.comp {A Y Y' : Scheme.{0}} {𝓜 : A.Modules} {p : Y ⟶ A} (h : Triv 𝓜 p) (r : Y' ⟶ Y) :
    Triv 𝓜 (r ≫ p) := by
  obtain ⟨e⟩ := h
  exact ⟨((Scheme.Modules.pullbackComp r p).app 𝓜).symm ≪≫ (Scheme.Modules.pullback r).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso r⟩

theorem Triv.congr {A Y : Scheme.{0}} {𝓜 : A.Modules} {p p' : Y ⟶ A} (h : Triv 𝓜 p) (e : p = p') : Triv 𝓜 p' := by
  subst e; exact h

theorem Triv.of_pullback_pullback {A Y Y' : Scheme.{0}} {𝓜 : A.Modules} (p : Y ⟶ A) (q : Y' ⟶ Y)
    (h : Nonempty ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback p).obj 𝓜) ≅
      (Scheme.Modules.pullback q).obj (𝟙_ Y.Modules))) : Triv 𝓜 (q ≫ p) := by
  obtain ⟨e⟩ := h
  exact ⟨((Scheme.Modules.pullbackComp q p).app 𝓜).symm ≪≫ e ≪≫ Scheme.Modules.pullbackUnitIso q⟩

theorem Triv.pullback_pullback {A Y Y' : Scheme.{0}} {𝓜 : A.Modules} (p : Y ⟶ A) (q : Y' ⟶ Y)
    (h : Triv 𝓜 (q ≫ p)) :
    Nonempty ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback p).obj 𝓜) ≅
      (Scheme.Modules.pullback q).obj (𝟙_ Y.Modules)) := by
  obtain ⟨e⟩ := h
  exact ⟨(Scheme.Modules.pullbackComp q p).app 𝓜 ≪≫ e ≪≫ (Scheme.Modules.pullbackUnitIso q).symm⟩

end PicInj

open PicInj in
theorem solution
    (k : Type) [Field k] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of k)) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (k' : Type) [Field k'] (φ : k →+* k')
    (h : Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj 𝓜 ≅
      𝟙_ ((Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).Modules))) :
    Nonempty (𝓜 ≅ 𝟙_ A.Modules) := by
  classical

  letI algk' : Algebra k k' := φ.toAlgebra
  haveI : IsProper f := hA.proper

  obtain ⟨ι, instP, instN, instD, S, instCR, instAlg, instFP, t, c, hDS, hDL⟩ :=
    Algebra.exists_isDirectLimit_of_finitePresentation k k'
  letI := instP; letI := instN; letI := instD; letI := instCR; letI := instAlg; haveI := hDS
  let i₀ : ι := Classical.arbitrary ι

  let X : Scheme.{0} := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (S i₀))))
  let fX : X ⟶ Spec (CommRingCat.of (S i₀)) := pullback.snd f _
  haveI : QuasiCompact fX := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : QuasiSeparated fX := MorphismProperty.pullback_snd _ _ inferInstance
  have hcomp₀ : (c i₀).toRingHom.comp (algebraMap k (S i₀)) = φ := (c i₀).comp_algebraMap

  let eR : pullback fX (Spec.map (CommRingCat.ofHom (c i₀).toRingHom)) ⟶ pullback f (Spec.map (CommRingCat.ofHom φ)) :=
    pullback.lift (pullback.fst fX _ ≫ pullback.fst f _) (pullback.snd fX _)
      (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, hcomp₀])
  have hTrivR : Triv 𝓜 (pullback.fst fX (Spec.map (CommRingCat.ofHom (c i₀).toRingHom)) ≫ pullback.fst f _) :=
    ((show Triv 𝓜 (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) from h).comp eR).congr (pullback.lift_fst _ _ _)
  obtain ⟨j, hij, ej⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
      (fun i j h => (t i j h).toRingHom) (fun i => (c i).toRingHom) hDL i₀ fX
      ((Scheme.Modules.pullback (pullback.fst f _)).obj 𝓜) (𝟙_ X.Modules)
      (h𝓜.pullback _) (Scheme.Modules.isInvertible_unit X) (hTrivR.pullback_pullback _ _)
  have hTrivj : Triv 𝓜 (pullback.fst fX (Spec.map (CommRingCat.ofHom (t i₀ j hij).toRingHom)) ≫ pullback.fst f _) :=
    Triv.of_pullback_pullback _ _ ej

  haveI : Nontrivial (S j) := (c j).toRingHom.domain_nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (S j)
  letI : Field (S j ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (S j) := inferInstance
  haveI : Module.Finite k (S j ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (S j ⧸ m)
  haveI : Module.FaithfullyFlat k (S j ⧸ m) := inferInstance

  let L : RelativeGroupLaw k f := hA.hasGroupLaw.some
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f := L.one (𝟙 _)
  let t₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) := 𝟙 _
  let M₀ : (pullback f t₀).Modules := (Scheme.Modules.pullback (pullback.fst f t₀)).obj 𝓜
  have hM₀ : Scheme.Modules.IsInvertible M₀ := h𝓜.pullback _
  let M₁ : RigidifiedLineBundle f ε t₀ :=
    { L := M₀
      isInvertible := hM₀
      rigidified := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field_monoidalV2 k _
        (hM₀.pullback (rigSection f t₀ ε)) }
  let M₂ : RigidifiedLineBundle f ε t₀ := RigidifiedLineBundle.unit t₀
  have hM₁ : Nonempty (M₁.L ≅ M₀) := ⟨Iso.refl _⟩
  let ψ : SchemeHomOver (pullback.snd t₀ (Scheme.TwoAffineOpenCover.specMap k (S j ⧸ m)) ≫
      Scheme.TwoAffineOpenCover.specMap k (S j ⧸ m)) t₀ :=
    ⟨pullback.fst t₀ (Scheme.TwoAffineOpenCover.specMap k (S j ⧸ m)), pullback.condition⟩

  have halg : algebraMap k (S j ⧸ m) =
      (Ideal.Quotient.mk m).comp ((t i₀ j hij).toRingHom.comp (algebraMap k (S i₀))) :=
    RingHom.ext fun x => by
      change algebraMap k (S j ⧸ m) x = Ideal.Quotient.mk m ((t i₀ j hij) (algebraMap k (S i₀) x))
      rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap]
  let Y₃ := pullback f (pullback.snd t₀ (Scheme.TwoAffineOpenCover.specMap k (S j ⧸ m)) ≫
      Scheme.TwoAffineOpenCover.specMap k (S j ⧸ m))
  let toSpecSj : Y₃ ⟶ Spec (CommRingCat.of (S j)) :=
    pullback.snd f _ ≫ pullback.snd t₀ _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))
  let y₁ : Y₃ ⟶ X :=
    pullback.lift (pullback.fst f _) (toSpecSj ≫ Spec.map (CommRingCat.ofHom (t i₀ j hij).toRingHom))
      (by
        simp only [toSpecSj, Category.assoc]
        rw [pullback.condition, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← CommRingCat.ofHom_comp, ← halg])
  let y : Y₃ ⟶ pullback fX (Spec.map (CommRingCat.ofHom (t i₀ j hij).toRingHom)) :=
    pullback.lift y₁ toSpecSj (by simp only [y₁, fX, pullback.lift_snd])
  have hTriv₃ : Triv 𝓜 (pullback.fst f (pullback.snd t₀ (Scheme.TwoAffineOpenCover.specMap k (S j ⧸ m)) ≫
      Scheme.TwoAffineOpenCover.specMap k (S j ⧸ m))) :=
    (hTrivj.comp y).congr (by simp only [y, y₁, pullback.lift_fst_assoc, pullback.lift_fst])
  have hbcs : baseChangeSnd f ψ ≫ pullback.fst f t₀ = pullback.fst f _ := by
    simp only [baseChangeSnd, pullback.lift_fst, Category.comp_id]
  have hψ : Nonempty ((M₁.pullbackAlong ψ).L ≅ (M₂.pullbackAlong ψ).L) := by
    obtain ⟨e₁⟩ := hM₁
    obtain ⟨e₃⟩ := (hTriv₃.congr hbcs.symm)
    exact ⟨(Scheme.Modules.pullback (baseChangeSnd f ψ)).mapIso e₁ ≪≫
      (Scheme.Modules.pullbackComp (baseChangeSnd f ψ) (pullback.fst f t₀)).app 𝓜 ≪≫ e₃ ≪≫
      (Scheme.Modules.pullbackUnitIso (baseChangeSnd f ψ)).symm⟩

  have hdesc := RigidifiedLineBundle.nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections k f ε
    (fun T _ _ => hA.bijective_algebraMap_sections_pullback T) (S j ⧸ m) t₀ M₁ M₂ hψ
  have hTriv₀ : Triv 𝓜 (pullback.fst f t₀) := by
    obtain ⟨e₁⟩ := hM₁
    obtain ⟨e⟩ := hdesc
    exact ⟨e₁.symm ≪≫ e⟩

  let s : A ⟶ pullback f t₀ := pullback.lift (𝟙 A) f (by simp [t₀])
  obtain ⟨e⟩ := (hTriv₀.comp s).congr (pullback.lift_fst _ _ _)
  exact ⟨((Scheme.Modules.pullbackId A).app 𝓜).symm ≪≫ e⟩

end

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_nonempty_pullback_iso_tensorUnit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_nonempty_pullback_iso_tensorUnit (solution)
