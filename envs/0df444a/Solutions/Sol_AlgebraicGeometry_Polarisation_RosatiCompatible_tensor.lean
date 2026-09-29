-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.RosatiCompatible.tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/151722e6-8744-593c-a7c8-9b95f5feec37

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_RosatiCompatible_tensor

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace CF6bTensorBody

noncomputable def inverseUnique {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {L M M' : C} (e : L ⊗ M ≅ 𝟙_ C) (e' : L ⊗ M' ≅ 𝟙_ C) : M ≅ M' :=
  (λ_ M).symm ≪≫ (e'.symm ⊗ᵢ Iso.refl M) ≪≫ (β_ L M' ⊗ᵢ Iso.refl M) ≪≫ α_ M' L M ≪≫
    (Iso.refl M' ⊗ᵢ e) ≪≫ ρ_ M'

noncomputable def swap4 {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] (W X Y Z : C) :
    (W ⊗ X) ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  α_ W X (Y ⊗ Z) ≪≫ whiskerLeftIso W ((α_ X Y Z).symm ≪≫ (β_ X Y ⊗ᵢ Iso.refl Z) ≪≫ α_ Y X Z) ≪≫ (α_ W Y (X ⊗ Z)).symm

variable {X : Scheme}

theorem nonempty_dual_tensor_iso {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M) :
    Nonempty (Scheme.Modules.dual (L ⊗ M) ≅ Scheme.Modules.dual L ⊗ Scheme.Modules.dual M) := by
  obtain ⟨e₁⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 (Scheme.Modules.IsInvertible.tensor_monoidalV2 hL hM)).2
  obtain ⟨eL⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hL).2
  obtain ⟨eM⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hM).2
  have e₂ : (L ⊗ M) ⊗ (Scheme.Modules.dual L ⊗ Scheme.Modules.dual M) ≅ 𝟙_ X.Modules :=
    swap4 L M (Scheme.Modules.dual L) (Scheme.Modules.dual M) ≪≫ (eL ⊗ᵢ eM) ≪≫ λ_ _
  exact ⟨inverseUnique e₁ e₂⟩

end CF6bTensorBody

open CF6bTensorBody in
theorem solution
    {S : Type} [CommRing S] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (𝓛 𝓛' : A.Modules) (h : Scheme.Modules.IsInvertible 𝓛) (h' : Scheme.Modules.IsInvertible 𝓛')
    (hR : RosatiCompatible f L 𝓛 act act_over star) (hR' : RosatiCompatible f L 𝓛' act act_over star) :
    RosatiCompatible f L (𝓛 ⊗ 𝓛') act act_over star := by
  intro b
  obtain ⟨ed⟩ := nonempty_dual_tensor_iso h h'

  let m := addMor f L
  let q₁ := pullback.fst f f
  let q₂ := pullback.snd f f
  have eΛ : mumfordBundle f L (𝓛 ⊗ 𝓛') ≅ mumfordBundle f L 𝓛 ⊗ mumfordBundle f L 𝓛' :=
    (Scheme.Modules.pullbackTensorObjIso m 𝓛 𝓛' ⊗ᵢ
      (((Scheme.Modules.pullback q₁).mapIso ed ≪≫ Scheme.Modules.pullbackTensorObjIso q₁ _ _) ⊗ᵢ
       ((Scheme.Modules.pullback q₂).mapIso ed ≪≫ Scheme.Modules.pullbackTensorObjIso q₂ _ _))) ≪≫
    (Iso.refl _ ⊗ᵢ swap4 _ _ _ _) ≪≫
    (swap4 ((Scheme.Modules.pullback m).obj 𝓛) (((Scheme.Modules.pullback q₁).obj (Scheme.Modules.dual 𝓛)) ⊗ ((Scheme.Modules.pullback q₂).obj (Scheme.Modules.dual 𝓛)))
      ((Scheme.Modules.pullback m).obj 𝓛') (((Scheme.Modules.pullback q₁).obj (Scheme.Modules.dual 𝓛')) ⊗ ((Scheme.Modules.pullback q₂).obj (Scheme.Modules.dual 𝓛')))).symm

  have E := LocIsoOnBase.equivalence (pullback.fst f f ≫ f)
  have key := LocIsoOnBase.tensor (hR b) (hR' b)
  refine E.trans ?_ (E.trans key ?_)
  · exact fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso
      ((Scheme.Modules.pullback _).mapIso eΛ ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _)⟩⟩
  · exact fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso
      ((Scheme.Modules.pullback _).mapIso eΛ ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _).symm⟩⟩

end S_AlgebraicGeometry_Polarisation_RosatiCompatible_tensor
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_RosatiCompatible_tensor (solution)
