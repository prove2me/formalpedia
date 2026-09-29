-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigidifiedLineBundle.fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/175fb513-7a4c-5c6a-9f32-21cf4da86ab9

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isAlgEquivZero_twistModule_fibre
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top IsProper Scheme.Modules.pullback GeometricallyIntegral Spec Scheme IsSeparated Scheme.Modules Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.dual RelEffCartierDiv graphOver RelEffCartierDiv.ofPoint RelEffCartierDiv.ofPoint_I Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top Scheme.Modules.pullbackTensorUnitObjIso RelEffCartierDiv.isInvertible_I Scheme.Modules.rigidify RelEffCartierDiv.isAlgEquivZero_twistModule_fibre RelEffCartierDiv.exists_I_eq_mul Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "rigSection RigidifiedLineBundle IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso fibrewiseAlgEquivZero_unit pointsSubBasepointModule rigSection_eq_graphOver sectionIdeal"
namespace PointsCut
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {k : Type u} [Field k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)

noncomputable def mid4 {X : Scheme.{u}} (W X' Y Z : X.Modules) : (W ⊗ X') ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X' ⊗ Z) :=
  α_ _ _ _ ≪≫ whiskerLeftIso W ((α_ _ _ _).symm ≪≫ whiskerRightIso (β_ X' Y) Z ≪≫ α_ _ _ _) ≪≫ (α_ _ _ _).symm

theorem rigSection_eq_graphOver :
    rigSection c (𝟙 (Spec (CommRingCat.of k))) ε = graphOver c ε.1 ε.2 := by
  apply pullback.hom_ext
  · simp [rigSection, graphOver]
  · simp [rigSection, graphOver]

theorem sectionIdeal_eq :
    sectionIdeal c ε (𝟙 (Spec (CommRingCat.of k))) = (RelEffCartierDiv.ofPoint c ε.1 ε.2).I := by
  rw [RelEffCartierDiv.ofPoint_I, sectionIdeal, rigSection_eq_graphOver]

theorem isInvertible_sectionIdeal_pow (n : ℕ) :
    ((sectionIdeal c ε (𝟙 (Spec (CommRingCat.of k)))) ^ n).IsInvertible := by
  induction n with
  | zero => rw [pow_zero, Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul (by rw [sectionIdeal_eq]; exact RelEffCartierDiv.isInvertible_I _)

theorem exists_div (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :
    ∀ (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)),
      ∃ (d : ℕ) (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of k)))),
        Nonempty (D.I.invModule ⊗ ((sectionIdeal c ε (𝟙 (Spec (CommRingCat.of k)))) ^ d).module ≅
          pointsSubBasepointModule (a := c) ε (P :: Ps)) := by
  intro Ps
  induction Ps generalizing P with
  | nil =>
    refine ⟨1, RelEffCartierDiv.ofPoint c P.1 P.2, ⟨?_⟩⟩
    refine whiskerLeftIso _ (eqToIso ?_) ≪≫ (ρ_ _).symm
    rw [pow_one, sectionIdeal_eq]
  | cons Q Ps ih =>
    obtain ⟨d, D', ⟨e'⟩⟩ := ih Q
    obtain ⟨F, hF⟩ := RelEffCartierDiv.exists_I_eq_mul (RelEffCartierDiv.ofPoint c P.1 P.2) D'
    refine ⟨1 + d, F, ⟨?_⟩⟩
    have hP : (RelEffCartierDiv.ofPoint c P.1 P.2).I.IsInvertible := RelEffCartierDiv.isInvertible_I _
    have hD' : D'.I.IsInvertible := RelEffCartierDiv.isInvertible_I _
    have hε1 : (sectionIdeal c ε (𝟙 (Spec (CommRingCat.of k)))).IsInvertible := by
      simpa using isInvertible_sectionIdeal_pow ε 1
    have hεd := isInvertible_sectionIdeal_pow ε d

    have i1 : F.I.invModule ≅ (RelEffCartierDiv.ofPoint c P.1 P.2).I.invModule ⊗ D'.I.invModule :=
      eqToIso (by rw [hF]) ≪≫ (Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hP hD').some
    have i2 : ((sectionIdeal c ε (𝟙 (Spec (CommRingCat.of k)))) ^ (1 + d)).module ≅
        (RelEffCartierDiv.ofPoint c ε.1 ε.2).I.module ⊗ ((sectionIdeal c ε (𝟙 (Spec (CommRingCat.of k)))) ^ d).module :=
      eqToIso (by rw [pow_add, pow_one]) ≪≫
        (Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor hε1 hεd).some ≪≫
        whiskerRightIso (eqToIso (by rw [sectionIdeal_eq])) _
    exact (i1 ⊗ᵢ i2) ≪≫ mid4 _ _ _ _ ≪≫ whiskerLeftIso _ e'

theorem nonempty_rigidify_iso (L : (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules)
    (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify (rigSection c (𝟙 (Spec (CommRingCat.of k))) ε)
      (pullback.snd c (𝟙 (Spec (CommRingCat.of k)))) L ≅ L) := by

  obtain ⟨i⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ (hL.pullback (rigSection c (𝟙 _) ε))
  obtain ⟨-, ⟨p⟩⟩ := (hL.pullback (rigSection c (𝟙 (Spec (CommRingCat.of k))) ε)).dual
  have j : Scheme.Modules.dual ((Scheme.Modules.pullback (rigSection c (𝟙 (Spec (CommRingCat.of k))) ε)).obj L) ≅
      𝟙_ _ :=
    (λ_ _).symm ≪≫ whiskerRightIso i.symm _ ≪≫ p
  exact ⟨whiskerLeftIso L ((Scheme.Modules.pullback _).mapIso j ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _) ≪≫ ρ_ L⟩

end AlgebraicGeometry.RelPicard.PointsCut

open AlgebraicGeometry.RelPicard.PointsCut in
theorem solution
    {k : Type u} [Field k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c}
    (N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))))
    (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c))
    (e : N.L ≅ pointsSubBasepointModule (a := c) ε Ps) :
    FibrewiseAlgEquivZero N := by
  cases Ps with
  | nil =>

    exact (fibrewiseAlgEquivZero_unit (c := c) (ε := ε) (𝟙 _)).congr ⟨e.symm⟩
  | cons P Ps =>
    obtain ⟨d, D, ⟨eD⟩⟩ := exists_div ε P Ps

    have hDI : Scheme.Modules.IsInvertible (D.I.invModule ⊗ ((sectionIdeal c ε (𝟙 (Spec (CommRingCat.of k)))) ^ d).module) :=
      (RelEffCartierDiv.isInvertible_I D).isInvertible_invModule.tensor (isInvertible_sectionIdeal_pow ε d).isInvertible_module
    obtain ⟨rg⟩ := nonempty_rigidify_iso ε _ hDI
    have eN : N.L ≅ D.twistModule c ε := e ≪≫ eD.symm ≪≫ rg.symm
    intro k' _ _ s
    exact IsAlgEquivZero.of_iso ((Scheme.Modules.pullback _).mapIso eN.symm)
      (RelEffCartierDiv.isAlgEquivZero_twistModule_fibre c ε D k' s)

end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule (solution)
