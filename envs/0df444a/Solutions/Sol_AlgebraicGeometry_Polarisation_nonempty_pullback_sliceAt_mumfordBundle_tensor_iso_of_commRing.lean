-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_pullback_sliceAt_mumfordBundle_tensor_iso_of_commRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f9e3be6f-db2d-5646-8e84-a31175f8e581

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_tensor_iso_of_commRing

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace SliceHelpers

p2m_open "CategoryTheory.MonoidalCategory"

variable {C : Type*} [Category C] [MonoidalCategory C]

noncomputable def swapMiddle [BraidedCategory C] (W X Y Z : C) : (W ⊗ X) ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  α_ W X (Y ⊗ Z) ≪≫ whiskerLeftIso W ((α_ X Y Z).symm ≪≫ whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z) ≪≫
    (α_ W Y (X ⊗ Z)).symm

noncomputable def shuffle6 [BraidedCategory C] (a a' b b' c c' : C) :
    (a ⊗ a') ⊗ ((b ⊗ b') ⊗ (c ⊗ c')) ≅ (a ⊗ (b ⊗ c)) ⊗ (a' ⊗ (b' ⊗ c')) :=
  whiskerLeftIso (a ⊗ a') (swapMiddle b b' c c') ≪≫ swapMiddle a a' (b ⊗ c) (b' ⊗ c')

noncomputable def isoOfTensorIsoUnit [BraidedCategory C] {A B D : C} (eB : A ⊗ B ≅ 𝟙_ C) (eD : A ⊗ D ≅ 𝟙_ C) : B ≅ D :=
  (λ_ B).symm ≪≫ whiskerRightIso ((β_ D A ≪≫ eD).symm) B ≪≫ α_ D A B ≪≫ whiskerLeftIso D eB ≪≫ ρ_ D

end SliceHelpers

theorem solution
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) (𝓛 𝓛' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t f) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L (𝓛 ⊗ 𝓛')) ≅ (Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) ⊗ (Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛')) := by
  classical

  obtain ⟨hd, ⟨e₁⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛
  obtain ⟨hd', ⟨e₂⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛'
  obtain ⟨-, ⟨e₁₂⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 (Scheme.Modules.IsInvertible.tensor_monoidalV2 h𝓛 h𝓛')

  let eD : (𝓛 ⊗ 𝓛') ⊗ (Scheme.Modules.dual 𝓛 ⊗ Scheme.Modules.dual 𝓛') ≅ 𝟙_ A.Modules :=
    SliceHelpers.swapMiddle 𝓛 𝓛' (Scheme.Modules.dual 𝓛) (Scheme.Modules.dual 𝓛') ≪≫ (e₁ ⊗ᵢ e₂) ≪≫ λ_ (𝟙_ A.Modules)
  let dT : Scheme.Modules.dual (𝓛 ⊗ 𝓛') ≅ Scheme.Modules.dual 𝓛 ⊗ Scheme.Modules.dual 𝓛' :=
    SliceHelpers.isoOfTensorIsoUnit e₁₂ eD

  let μ := addMor f L
  let p₁ := pullback.fst f f
  let p₂ := pullback.snd f f
  let eΛ : mumfordBundle f L (𝓛 ⊗ 𝓛') ≅ mumfordBundle f L 𝓛 ⊗ mumfordBundle f L 𝓛' :=
    (Scheme.Modules.pullbackTensorObjIso μ 𝓛 𝓛' ⊗ᵢ
      (((Scheme.Modules.pullback p₁).mapIso dT ≪≫ Scheme.Modules.pullbackTensorObjIso p₁ _ _) ⊗ᵢ
        ((Scheme.Modules.pullback p₂).mapIso dT ≪≫ Scheme.Modules.pullbackTensorObjIso p₂ _ _))) ≪≫
      SliceHelpers.shuffle6 _ _ _ _ _ _
  exact ⟨(Scheme.Modules.pullback (sliceAt f x)).mapIso eΛ ≪≫ Scheme.Modules.pullbackTensorObjIso (sliceAt f x) _ _⟩

end S_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_tensor_iso_of_commRing
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_tensor_iso_of_commRing (solution)
