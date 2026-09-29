-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.flat_surjective_restrictPair_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7b2d172f-ec6e-5536-946a-51aaa224d55a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_restrictHom_pair_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_opens_section_restrictPair_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_iso_preimage_restrictPair_pullback_torus_of_section_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_flat_surjective_restrictPair_of_twoGluedSmoothCurves
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SplitTorus

namespace S1C

theorem flat_torusStr (k : Type u) [Field k] (n : ℕ) : Flat (torusStr k n) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  show (algebraMap k (torusCoord k n)).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

theorem surjective_torusStr (k : Type u) [Field k] (n : ℕ) : Surjective (torusStr k n) := by
  refine ⟨fun p => ?_⟩
  haveI : Nonempty ↥(torusScheme k n) := inferInstance
  exact ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩

end S1C

open S1C in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (ε : SchemeHomOver (𝟙 _) x) (ε₁ : SchemeHomOver (𝟙 _) c₁) (hε : ε₁.1 ≫ i₁.1 = ε.1)
    (ε₂ : SchemeHomOver (𝟙 _) c₂)
    (D : RelativePic0Designation k x) (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (D₁ : RelativePic0Designation k c₁) (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase)
    (hν₁ : ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
    (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L))) :
    Flat (pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm) : D.P ⟶ pullback D₁.toBase D₂.toBase) ∧
    Surjective (pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm) : D.P ⟶ pullback D₁.toBase D₂.toBase) := by

  obtain ⟨ν₁', ν₂', hν₁', hν₂', hmul₁, hmul₂⟩ :=
    AlgebraicGeometry.RelPicard.exists_restrictHom_pair_of_twoGluedSmoothCurves x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0
      ε ε₁ hε ε₂ D hD D₁ hD₁ D₂ hD₂
  have e₁ : ν₁' = ν₁ := hν₁'.trans hν₁.symm
  have e₂ : ν₂' = ν₂ := by
    have key := hD₂.ext_of_iso D.toBase
      (NeronModelInfra.schemeHomOverComp (schemeHomOverId D.toBase) ν₂')
      (NeronModelInfra.schemeHomOverComp (schemeHomOverId D.toBase) ν₂)
      ⟨(hν₂' D.toBase (schemeHomOverId D.toBase)).some ≪≫ (hν₂ D.toBase (schemeHomOverId D.toBase)).some.symm⟩
    simpa only [schemeHomOverComp_id_left] using key
  subst e₁ e₂

  obtain ⟨τ, hτ, -, hτker⟩ :=
    AlgebraicGeometry.RelPicard.exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves x hXred c₁ c₂
      i₁ i₂ hjs hcr s hs hs0 ε ε₁ hε ε₂ D hD D₁ hD₁ D₂ hD₂ ν₁' ν₂' hν₁ hν₂

  haveI := flat_torusStr k (s - 1)
  haveI := surjective_torusStr k (s - 1)
  refine AlgebraicGeometry.flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst
    (torusStr k (s - 1)) (pullback.fst D₁.toBase D₂.toBase ≫ D₁.toBase)
    (pullback.lift ν₁'.1 ν₂'.1 (ν₁'.2.trans ν₂'.2.symm)) fun p => ?_
  obtain ⟨U, hpU, σ, hσ⟩ :=
    AlgebraicGeometry.RelPicard.exists_opens_section_restrictPair_of_twoGluedSmoothCurves x hXred c₁ c₂ i₁ i₂ hjs hcr
      s hs hs0 ε ε₁ hε ε₂ D hD D₁ hD₁ D₂ hD₂ ν₁' ν₂' hν₁ hν₂ p
  obtain ⟨e, he⟩ :=
    AlgebraicGeometry.RelPicard.exists_iso_preimage_restrictPair_pullback_torus_of_section_of_twoGluedSmoothCurves
      x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 ε ε₁ hε ε₂ D hD D₁ hD₁ D₂ hD₂ ν₁' ν₂' hν₁ hν₂
      hmul₁ hmul₂ τ hτ hτker U σ hσ
  exact ⟨U, hpU, e, he⟩

end S_AlgebraicGeometry_RelPicard_flat_surjective_restrictPair_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_flat_surjective_restrictPair_of_twoGluedSmoothCurves (solution)
