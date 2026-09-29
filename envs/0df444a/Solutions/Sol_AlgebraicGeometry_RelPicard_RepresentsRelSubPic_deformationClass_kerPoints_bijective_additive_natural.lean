-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.deformationClass_kerPoints_bijective_additive_natural
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/fe2d6fcd-be23-567e-a184-202c80855b59

import Mathlib
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPointsToRigKer_bijective
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPointsToRigKer_mul
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_mul_mem_and_comp_mem
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_injective
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_map_mul
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_natural
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_deformationClass_kerPoints_bijective_additive_natural
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_deformationClass_kerPoints_bijective_additive_natural.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_deformationClass_kerPoints_bijective_additive_natural.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Scheme.TwoAffineOpenCover"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec Spec.map Scheme Scheme.TwoAffineOpenCover"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "dualNumberReduction dualNumberReduction_comp_specMap RigKerDualNumber.Carrier RigKerDualNumber RepresentsRelSubPic.kerPointsToRigKer RepresentsRelSubPic algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw LFP.stageHom H1StructureSheaf IsDeformationClassMap RepresentsRelSubPic.kerPoints_mul_mem_and_comp_mem IsDeformationClassMap.natural"
namespace DeltaRow
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {c : X ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}

section Stage
variable (R)
variable (A : Type u) [CommRing A] [Algebra R A] (A' : Type u) [CommRing A'] [Algebra R A'] (g : A →ₐ[R] A')

abbrev liftHom : DualNumber A →ₐ[R] DualNumber A' :=
  DualNumber.lift ⟨((IsScalarTower.toAlgHom R A' (DualNumber A')).comp g, DualNumber.eps),
    DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩

abbrev stageOver : SchemeHomOver (specMap R (DualNumber A')) (specMap R (DualNumber A)) :=
  LFP.stageHom R (liftHom R A A' g)

theorem fstHom_comp_liftHom :
    (TrivSqZeroExt.fstHom R A' A').toRingHom.comp (liftHom R A A' g).toRingHom =
      g.toRingHom.comp (TrivSqZeroExt.fstHom R A A).toRingHom := by
  refine DualNumber.ringHom_ext ?_ ?_
  · ext a
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TrivSqZeroExt.fstHom_apply, DualNumber.lift_apply_inl, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TrivSqZeroExt.fstHom_apply, DualNumber.lift_apply_eps, DualNumber.fst_eps, map_zero]

theorem dualNumberReduction_comp_stage :
    dualNumberReduction R A' ≫ (stageOver R A A' g).1 = (LFP.stageHom R g).1 ≫ dualNumberReduction R A := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (fstHom_comp_liftHom R A A' g)

end Stage

section K
variable (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

abbrev K (A : Type u) [CommRing A] [Algebra R A] : Type u :=
  { x : SchemeHomOver (specMap R (DualNumber A)) D.toBase //
      dualNumberReduction R A ≫ x.1 = ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one (specMap R A)).1 }

variable (A : Type u) [CommRing A] [Algebra R A]

theorem one_memK :
    dualNumberReduction R A ≫ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one (specMap R (DualNumber A))).1 = ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one (specMap R A)).1 :=
  congrArg Subtype.val ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one_natural _ _ (dualNumberReduction R A) (dualNumberReduction_comp_specMap R A))

theorem mul_memK (x y : K hD A) :
    dualNumberReduction R A ≫ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul (specMap R (DualNumber A)) x.1 y.1).1 = ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one (specMap R A)).1 :=
  (RepresentsRelSubPic.kerPoints_mul_mem_and_comp_mem hD A).1 x.1 y.1 x.2 y.2

def oneK : K hD A := ⟨(RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one _, one_memK hD A⟩

def mulK (x y : K hD A) : K hD A := ⟨(RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ x.1 y.1, mul_memK hD A x y⟩

variable {A}
variable {𝒱 : X.TwoAffineOpenCover} {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱}
  (hδ : IsDeformationClassMap c ε A 𝒱 δ)

abbrev Δ (x : K hD A) : H1StructureSheaf c A 𝒱 := δ (hD.kerPointsToRigKer A x)

include hδ in
theorem Δ_bijective : Function.Bijective (Δ hD (δ := δ)) :=
  Function.Bijective.comp ⟨hδ.injective, hδ.surjective⟩ (hD.kerPointsToRigKer_bijective A)

include hδ in
theorem Δ_mul (x y : K hD A) (h) :
    Δ hD (δ := δ) ⟨(RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ x.1 y.1, h⟩ = Δ hD (δ := δ) x + Δ hD (δ := δ) y := by
  unfold Δ
  rw [hD.kerPointsToRigKer_mul A x y h]
  exact hδ.map_mul _ _

include hδ in
theorem Δ_mulK (x y : K hD A) : Δ hD (δ := δ) (mulK hD A x y) = Δ hD (δ := δ) x + Δ hD (δ := δ) y :=
  Δ_mul hD hδ x y (mul_memK hD A x y)

include hδ in
theorem Δ_oneK : Δ hD (δ := δ) (oneK hD A) = 0 := by
  have h1 : mulK hD A (oneK hD A) (oneK hD A) = oneK hD A := Subtype.ext ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one_mul _ _)
  have h2 := Δ_mulK hD hδ (oneK hD A) (oneK hD A)
  rw [h1] at h2
  have h3 := congrArg (fun m => m - Δ hD (δ := δ) (oneK hD A)) h2
  simp only [sub_self, add_sub_cancel_right] at h3
  exact h3.symm

theorem kerPointsToRigKer_eq_mk (x : K hD A) :
    ∃ M : RigKerDualNumber.Carrier c ε A,
      hD.kerPointsToRigKer A x = Quotient.mk _ M ∧ M.1 = hD.poincare.pullbackAlong x.1 := by
  unfold RepresentsRelSubPic.kerPointsToRigKer
  exact ⟨_, rfl, rfl⟩

end K

section Restrict
variable (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
  (A : Type u) [CommRing A] [Algebra R A] (A' : Type u) [CommRing A'] [Algebra R A'] (g : A →ₐ[R] A')

theorem stage_mem (x : SchemeHomOver (specMap R (DualNumber A)) D.toBase)
    (hx : dualNumberReduction R A ≫ x.1 = ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one (specMap R A)).1) :
    dualNumberReduction R A' ≫ ((stageOver R A A' g).1 ≫ x.1) = ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one (specMap R A')).1 := by
  rw [← Category.assoc, dualNumberReduction_comp_stage, Category.assoc, hx]
  exact congrArg Subtype.val ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one_natural _ _ (LFP.stageHom R g).1 (LFP.stageHom R g).2)

def stageK (x : K hD A) : K hD A' :=
  ⟨GoodReductionJacobian.schemeHomOverComp (stageOver R A A' g).1 (stageOver R A A' g).2 x.1,
    stage_mem hD A A' g x.1 x.2⟩

variable {A A'}
variable {𝒱 : X.TwoAffineOpenCover}
  {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ)
  {δ' : RigKerDualNumber c ε A' → H1StructureSheaf c A' 𝒱} (hδ' : IsDeformationClassMap c ε A' 𝒱 δ')

include hδ hδ' in
theorem Δ_stageK (x : K hD A) :
    Δ hD (δ := δ') (stageK hD A A' g x) = 𝒱.H1stageMap c g (Δ hD (δ := δ) x) := by
  obtain ⟨M, hM, hM1⟩ := kerPointsToRigKer_eq_mk hD x
  obtain ⟨N, hN, hN1⟩ := kerPointsToRigKer_eq_mk hD (stageK hD A A' g x)
  unfold Δ
  rw [hM, hN]
  refine IsDeformationClassMap.natural hδ hδ' g M N ?_
  rw [hM1, hN1]
  exact ⟨hD.poincare.pullbackAlongPullbackAlongIso x.1 (stageOver R A A' g)⟩

end Restrict

end AlgebraicGeometry.RelPicard.DeltaRow

end

open AlgebraicGeometry.RelPicard.DeltaRow in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) {𝒱 : C.TwoAffineOpenCover}
    (A : Type u) [CommRing A] [Algebra R A]
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ) :
    letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h

    Function.Bijective (fun x => δ (h.kerPointsToRigKer A x)) ∧

    (∀ h1, δ (h.kerPointsToRigKer A ⟨L.one (specMap R (DualNumber A)), h1⟩) = 0) ∧

    (∀ (x y : {x : SchemeHomOver (specMap R (DualNumber A)) D.toBase //
          dualNumberReduction R A ≫ x.1 = (L.one (specMap R A)).1}) (hxy),
        δ (h.kerPointsToRigKer A ⟨L.mul _ x.1 y.1, hxy⟩) =
          δ (h.kerPointsToRigKer A x) + δ (h.kerPointsToRigKer A y)) ∧

    (∀ (A' : Type u) [CommRing A'] [Algebra R A'] (g : A →ₐ[R] A')
        (x : SchemeHomOver (specMap R (DualNumber A)) D.toBase),
        dualNumberReduction R A ≫ x.1 = (L.one (specMap R A)).1 →
        dualNumberReduction R A' ≫ ((LFP.stageHom R (DualNumber.lift
            ⟨((IsScalarTower.toAlgHom R A' (DualNumber A')).comp g, DualNumber.eps),
              DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).1 ≫ x.1) = (L.one (specMap R A')).1) ∧

    (∀ (A' : Type u) [CommRing A'] [Algebra R A'] {δ' : RigKerDualNumber c ε A' → H1StructureSheaf c A' 𝒱}
        (_ : IsDeformationClassMap c ε A' 𝒱 δ') (g : A →ₐ[R] A')
        (x : {x : SchemeHomOver (specMap R (DualNumber A)) D.toBase //
          dualNumberReduction R A ≫ x.1 = (L.one (specMap R A)).1}) (hx'),
        δ' (h.kerPointsToRigKer A' ⟨GoodReductionJacobian.schemeHomOverComp
            (LFP.stageHom R (DualNumber.lift
              ⟨((IsScalarTower.toAlgHom R A' (DualNumber A')).comp g, DualNumber.eps),
                DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).1
            (LFP.stageHom R (DualNumber.lift
              ⟨((IsScalarTower.toAlgHom R A' (DualNumber A')).comp g, DualNumber.eps),
                DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).2 x.1, hx'⟩) =
          𝒱.H1stageMap c g (δ (h.kerPointsToRigKer A x))) := by
  refine ⟨Δ_bijective h hδ, fun h1 => Δ_oneK h hδ, fun x y hxy => Δ_mul h hδ x y hxy,
    fun A' _ _ g x hx => stage_mem h A A' g x hx, fun A' _ _ δ' hδ' g x hx' => ?_⟩
  exact Δ_stageK h g hδ hδ' x

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_deformationClass_kerPoints_bijective_additive_natural
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_deformationClass_kerPoints_bijective_additive_natural (solution)
