-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsDeformationClassMap.map_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/14640356-8cb8-5a11-894d-d75c41b4837d

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_map_mul
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {A : Type u} [CommRing A] [Algebra R A] {𝒱 : C.TwoAffineOpenCover}
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ)
    (x y : RigKerDualNumber c ε A) :
    δ (RigKerDualNumber.mul c ε A x y) = δ x + δ y := by
  induction x using Quotient.ind with
  | _ M =>
  induction y using Quotient.ind with
  | _ N =>
  obtain ⟨e₀, e₁, f, h₀, h₁, hM⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒱 M
  obtain ⟨e₀', e₁', f', h₀', h₁', hN⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒱 N
  rw [hδ M e₀ e₁ f h₀ h₁ hM, hδ N e₀' e₁' f' h₀' h₁' hN]
  have h := hδ ⟨M.1.tensor N.1, RigKerDualNumber.tensor_mem c ε A M N⟩
    (Scheme.Modules.tensorSections e₀ e₀') (Scheme.Modules.tensorSections e₁ e₁') (f + f')
    (h₀.tensorSections h₀') (h₁.tensorSections h₁') ?_
  · rw [← Submodule.Quotient.mk_add, ← h]
    rfl
  · change (M.1.L ⊗ N.1.L).presheaf.map (homOfLE _).op (Scheme.Modules.tensorSections e₁ e₁') =
        _ • (M.1.L ⊗ N.1.L).presheaf.map (homOfLE _).op (Scheme.Modules.tensorSections e₀ e₀')
    rw [Scheme.Modules.map_homOfLE_tensorSections, Scheme.Modules.map_homOfLE_tensorSections, hM, hN,
      Scheme.Modules.tensorSections_smul_left, Scheme.Modules.tensorSections_smul_right, smul_smul]
    congr 1
    change oneAddEpsMul A 𝒱 c f * oneAddEpsMul A 𝒱 c f' = oneAddEpsMul A 𝒱 c (f + f')
    simp only [oneAddEpsMul, map_add]
    have he : algebraMap (DualNumber A)
        ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01 DualNumber.eps *
        algebraMap (DualNumber A) _ DualNumber.eps = 0 := by
      rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    linear_combination ((dualNumberThickening A 𝒱 c).map01 f * (dualNumberThickening A 𝒱 c).map01 f') * he

end S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_map_mul
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_map_mul (solution)
