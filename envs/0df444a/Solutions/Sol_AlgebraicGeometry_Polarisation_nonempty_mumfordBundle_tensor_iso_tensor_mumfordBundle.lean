-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_tensor_iso_tensor_mumfordBundle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/13ae85ec-2c48-5836-bb35-b5a2ba56368d

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_tensor_iso_tensor_mumfordBundle

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace LambdaTensor29

noncomputable def inverseUnique {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {L M M' : C} (e : L ⊗ M ≅ 𝟙_ C) (e' : L ⊗ M' ≅ 𝟙_ C) : M ≅ M' :=
  (λ_ M).symm ≪≫ (e'.symm ⊗ᵢ Iso.refl M) ≪≫ (β_ L M' ⊗ᵢ Iso.refl M) ≪≫ α_ M' L M ≪≫
    (Iso.refl M' ⊗ᵢ e) ≪≫ ρ_ M'

noncomputable def swap4 {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] (W X Y Z : C) :
    (W ⊗ X) ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  α_ W X (Y ⊗ Z) ≪≫ whiskerLeftIso W ((α_ X Y Z).symm ≪≫ (β_ X Y ⊗ᵢ Iso.refl Z) ≪≫ α_ Y X Z) ≪≫ (α_ W Y (X ⊗ Z)).symm

variable {X : Scheme.{u}}

theorem nonempty_dual_tensor_iso {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M) :
    Nonempty (Scheme.Modules.dual (L ⊗ M) ≅ Scheme.Modules.dual L ⊗ Scheme.Modules.dual M) := by
  obtain ⟨e₁⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 (Scheme.Modules.IsInvertible.tensor_monoidalV2 hL hM)).2
  obtain ⟨eL⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hL).2
  obtain ⟨eM⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hM).2
  have e₂ : (L ⊗ M) ⊗ (Scheme.Modules.dual L ⊗ Scheme.Modules.dual M) ≅ 𝟙_ X.Modules :=
    swap4 L M (Scheme.Modules.dual L) (Scheme.Modules.dual M) ≪≫ (eL ⊗ᵢ eM) ≪≫ λ_ _
  exact ⟨inverseUnique e₁ e₂⟩

end LambdaTensor29

open LambdaTensor29

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (N N' : A.Modules) (hN : Scheme.Modules.IsInvertible N) (hN' : Scheme.Modules.IsInvertible N') :
    Nonempty (mumfordBundle f L (N ⊗ N') ≅ mumfordBundle f L N ⊗ mumfordBundle f L N') := by
  obtain ⟨ed⟩ := nonempty_dual_tensor_iso hN hN'
  let m := addMor f L
  let q₁ := pullback.fst f f
  let q₂ := pullback.snd f f
  exact ⟨(Scheme.Modules.pullbackTensorObjIso m N N' ⊗ᵢ
      (((Scheme.Modules.pullback q₁).mapIso ed ≪≫ Scheme.Modules.pullbackTensorObjIso q₁ _ _) ⊗ᵢ
       ((Scheme.Modules.pullback q₂).mapIso ed ≪≫ Scheme.Modules.pullbackTensorObjIso q₂ _ _))) ≪≫
    (Iso.refl _ ⊗ᵢ swap4 _ _ _ _) ≪≫
    (swap4 ((Scheme.Modules.pullback m).obj N)
      (((Scheme.Modules.pullback q₁).obj (Scheme.Modules.dual N)) ⊗ ((Scheme.Modules.pullback q₂).obj (Scheme.Modules.dual N)))
      ((Scheme.Modules.pullback m).obj N')
      (((Scheme.Modules.pullback q₁).obj (Scheme.Modules.dual N')) ⊗ ((Scheme.Modules.pullback q₂).obj (Scheme.Modules.dual N')))).symm⟩

end S_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_tensor_iso_tensor_mumfordBundle
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_tensor_iso_tensor_mumfordBundle (solution)
