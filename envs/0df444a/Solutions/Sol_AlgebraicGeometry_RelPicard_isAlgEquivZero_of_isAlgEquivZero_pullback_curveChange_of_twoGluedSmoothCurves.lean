-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4a84e631-29b4-5849-aa8d-946813811e1f

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard"

namespace S1C
namespace GlueAEZ

theorem isReduced_pullback_symm {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    (h : IsReduced (pullback f g)) : IsReduced (pullback g f) :=
  haveI := h
  isReduced_of_isOpenImmersion (pullbackSymmetry g f).hom

theorem natCard_pullback_symm {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X) :
    Nat.card ↥(pullback g f) = Nat.card ↥(pullback f g) :=
  Nat.card_congr (Scheme.homeoOfIso (pullbackSymmetry g f)).toEquiv

section Monoidal
variable {A B : Scheme.{u}} (f : B ⟶ A)

noncomputable def pullbackTensorIsoUnit {L P : A.Modules} (e : L ⊗ P ≅ 𝟙_ A.Modules) :
    (Scheme.Modules.pullback f).obj L ⊗ (Scheme.Modules.pullback f).obj P ≅ 𝟙_ B.Modules :=
  (Scheme.Modules.pullbackTensorObjIso f L P).symm ≪≫ (Scheme.Modules.pullback f).mapIso e ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso f

noncomputable def tensorTensorIsoUnit₁ {P Q R : A.Modules} (eP : P ≅ 𝟙_ _) (eQR : Q ⊗ R ≅ 𝟙_ _) :
    P ⊗ (Q ⊗ R) ≅ 𝟙_ A.Modules :=
  (eP ⊗ᵢ eQR) ≪≫ λ_ _

noncomputable def tensorTensorIsoUnit₂ {P Q R : A.Modules} (eQ : Q ≅ 𝟙_ _) (ePR : P ⊗ R ≅ 𝟙_ _) :
    P ⊗ (Q ⊗ R) ≅ 𝟙_ A.Modules :=
  whiskerLeftIso P ((eQ ⊗ᵢ Iso.refl R) ≪≫ λ_ R) ≪≫ ePR

end Monoidal

end S1C.GlueAEZ

open S1C.GlueAEZ in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (K : Type u) [Field K] [IsAlgClosed K] (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (L : (pullback x κ).Modules) (hL : Scheme.Modules.IsInvertible L)
    (h₁ : IsAlgEquivZero (pullback.snd c₁ κ) ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 κ)).obj L))
    (h₂ : IsAlgEquivZero (pullback.snd c₂ κ) ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 κ)).obj L)) :
    IsAlgEquivZero (pullback.snd x κ) L := by

  have hjs' : ∀ z : X, z ∈ Set.range i₂.1.base ∨ z ∈ Set.range i₁.1.base := fun z => (hjs z).symm
  have hcr' : IsReduced (pullback i₂.1 i₁.1) := isReduced_pullback_symm i₁.1 i₂.1 hcr
  have hs' : Nat.card ↥(pullback i₂.1 i₁.1) = s := (natCard_pullback_symm i₁.1 i₂.1).trans hs

  obtain ⟨L', hL', hL'aez, ⟨e₁'⟩, ⟨e₂'⟩⟩ :=
    AlgebraicGeometry.RelPicard.exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves
      x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 K κ _ (hL.pullback (curveChange i₁.1 i₁.2 κ)) h₁

  obtain ⟨L'', hL'', hL''aez, ⟨e₁''⟩, ⟨e₂''⟩⟩ :=
    AlgebraicGeometry.RelPicard.exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves
      x hXred c₂ c₁ i₂ i₁ hjs' hcr' s hs' hs0 K κ _ (hL.pullback (curveChange i₂.1 i₂.2 κ)) h₂

  obtain ⟨P', hP', ⟨eP'⟩⟩ := hL'.exists_tensor_inverse
  obtain ⟨P'', hP'', ⟨eP''⟩⟩ := hL''.exists_tensor_inverse

  have hN : Scheme.Modules.IsInvertible (P'' ⊗ (P' ⊗ L)) := hP''.tensor (hP'.tensor hL)
  have hN₁ : Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 κ)).obj (P'' ⊗ (P' ⊗ L)) ≅
      SheafOfModules.unit (pullback c₁ κ).ringCatSheaf) := by
    refine ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso _ _ _) ≪≫ tensorTensorIsoUnit₁ ?_ ?_⟩
    ·
      exact (λ_ _).symm ≪≫ (e₂''.symm ⊗ᵢ Iso.refl _) ≪≫ pullbackTensorIsoUnit _ eP''
    ·
      exact β_ _ _ ≪≫ (e₁'.symm ⊗ᵢ Iso.refl _) ≪≫ pullbackTensorIsoUnit _ eP'
  have hN₂ : Nonempty ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 κ)).obj (P'' ⊗ (P' ⊗ L)) ≅
      SheafOfModules.unit (pullback c₂ κ).ringCatSheaf) := by
    refine ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso _ _ _) ≪≫ tensorTensorIsoUnit₂ ?_ ?_⟩
    ·
      exact (λ_ _).symm ≪≫ (e₂'.symm ⊗ᵢ Iso.refl _) ≪≫ pullbackTensorIsoUnit _ eP'
    ·
      exact β_ _ _ ≪≫ (e₁''.symm ⊗ᵢ Iso.refl _) ≪≫ pullbackTensorIsoUnit _ eP''

  have hNaez : IsAlgEquivZero (pullback.snd x κ) (P'' ⊗ (P' ⊗ L)) :=
    AlgebraicGeometry.RelPicard.isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves
      x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 K κ _ hN hN₁ hN₂

  have hPL : IsAlgEquivZero (pullback.snd x κ) (P' ⊗ L) :=
    (hL''aez.tensor hNaez).of_iso ((α_ _ _ _).symm ≪≫ (eP'' ⊗ᵢ Iso.refl _) ≪≫ λ_ _)
  exact (hL'aez.tensor hPL).of_iso ((α_ _ _ _).symm ≪≫ (eP' ⊗ᵢ Iso.refl _) ≪≫ λ_ _)

end S_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves (solution)
