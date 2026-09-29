-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/93daf3f2-84ae-5c61-969e-c34d2d6bbd53

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_torus_ker_restrictPair_of_twoGluedSmoothCurves
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_comp_eq_one_iff
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_isClosedImmersion_of_iff_exists_comp_eq_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SplitTorus

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
    ∃ τ : SchemeHomOver (torusStr k (s - 1)) D.toBase,
      IsClosedImmersion τ.1 ∧
      (∀ χ χ' : WithConv (torusCoord k (s - 1) →ₐ[k] k),
        NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) (χ * χ').ofConv) τ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _
            (NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ.ofConv) τ)
            (NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ'.ofConv) τ)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        (NeronModelInfra.schemeHomOverComp a ν₁ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one t ∧
          NeronModelInfra.schemeHomOverComp a ν₂ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one t) ↔
        ∃ y : SchemeHomOver t (torusStr k (s - 1)), NeronModelInfra.schemeHomOverComp y τ = a) := by
  obtain ⟨τ, hhom, hker, hinj⟩ :=
    AlgebraicGeometry.RelPicard.exists_torus_ker_restrictPair_of_twoGluedSmoothCurves x hXred c₁ c₂ i₁ i₂ hjs hcr
      s hs hs0 ε ε₁ hε ε₂ D hD D₁ hD₁ D₂ hD₂ ν₁ ν₂ hν₁ hν₂
  obtain ⟨K, j, hj, hK⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_comp_eq_one_iff
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁)
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂) ν₁ ν₂
  refine ⟨τ, ?_, hhom, hker⟩
  haveI := hj
  haveI : IsDomain (torusCoord k (s - 1)) := inferInstance
  haveI : IsReduced (torusScheme k (s - 1)) := inferInstance
  haveI : IsSeparated (torusStr k (s - 1)) := inferInstance
  haveI : LocallyOfFiniteType (torusStr k (s - 1)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    show RingHom.FiniteType (algebraMap k (torusCoord k (s - 1)))
    rw [RingHom.finiteType_algebraMap]
    haveI : AddMonoid.FG (Fin (s - 1) → ℤ) := by
      rw [← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]; infer_instance
    infer_instance
  haveI : Flat (torusStr k (s - 1)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    show RingHom.Flat (algebraMap k (torusCoord k (s - 1)))
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  exact AlgebraicGeometry.SchemeHomOver.isClosedImmersion_of_iff_exists_comp_eq_of_injective
    (torusStr k (s - 1)) D.toBase τ j (fun t a => (hK t a).symm.trans (hker t a)) hinj

end S_AlgebraicGeometry_RelPicard_exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves (solution)
