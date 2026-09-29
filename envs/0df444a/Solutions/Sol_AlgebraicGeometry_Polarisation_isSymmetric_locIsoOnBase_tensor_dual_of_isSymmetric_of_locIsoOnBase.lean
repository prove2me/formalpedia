-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_tensor_dual_of_isSymmetric_of_locIsoOnBase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/667b8a71-71ea-57f7-816d-e0b3ce730f29

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_dual_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_dual_of_isSymmetric_of_locIsoOnBase

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace RootDiff

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem ofIso {M M' : A.Modules} (e : M ≅ M') : LocIsoOnBase f M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

def swapMiddle (a b c d : A.Modules) : (a ⊗ b) ⊗ (c ⊗ d) ≅ (a ⊗ c) ⊗ (b ⊗ d) :=
  α_ a b (c ⊗ d) ≪≫ whiskerLeftIso a ((α_ b c d).symm ≪≫ whiskerRightIso (β_ b c) d ≪≫ α_ c b d) ≪≫ (α_ a c (b ⊗ d)).symm

theorem main (L : RelativeGroupLaw R f)
    (𝓛 τ τ' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hτ : Scheme.Modules.IsInvertible τ) (hτ' : Scheme.Modules.IsInvertible τ')
    (hsτ : IsSymmetric f L τ) (hsτ' : IsSymmetric f L τ')
    (hrτ : LocIsoOnBase f 𝓛 (τ ⊗ (Scheme.Modules.pullback (negMor f L)).obj τ))
    (hrτ' : LocIsoOnBase f 𝓛 (τ' ⊗ (Scheme.Modules.pullback (negMor f L)).obj τ')) :
    IsSymmetric f L (τ' ⊗ Scheme.Modules.dual τ) ∧
      LocIsoOnBase f ((τ' ⊗ Scheme.Modules.dual τ) ⊗ (τ' ⊗ Scheme.Modules.dual τ)) (𝟙_ A.Modules) ∧
      Nonempty (τ ⊗ (τ' ⊗ Scheme.Modules.dual τ) ≅ τ') := by
  have E := LocIsoOnBase.equivalence f
  have hnτ : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (negMor f L)).obj τ) := hτ.pullback _
  obtain ⟨eτ⟩ := (hτ.dual_monoidalV2).2
  obtain ⟨e𝓛⟩ := (h𝓛.dual_monoidalV2).2
  obtain ⟨edτ⟩ := hτ.pullback_dual_monoidalV2 (negMor f L)
  obtain ⟨eττ⟩ := hτ.dual_tensor_monoidalV2 hτ

  have sqτ : LocIsoOnBase f 𝓛 (τ ⊗ τ) := E.trans hrτ (LocIsoOnBase.tensor (E.refl τ) hsτ)
  have sqτ' : LocIsoOnBase f 𝓛 (τ' ⊗ τ') := E.trans hrτ' (LocIsoOnBase.tensor (E.refl τ') hsτ')
  refine ⟨?_, ?_, ⟨?_⟩⟩
  ·
    show LocIsoOnBase f ((Scheme.Modules.pullback (negMor f L)).obj (τ' ⊗ Scheme.Modules.dual τ)) (τ' ⊗ Scheme.Modules.dual τ)
    have h1 : LocIsoOnBase f
        ((Scheme.Modules.pullback (negMor f L)).obj τ' ⊗ Scheme.Modules.dual ((Scheme.Modules.pullback (negMor f L)).obj τ))
        (τ' ⊗ Scheme.Modules.dual τ) :=
      LocIsoOnBase.tensor hsτ' (LocIsoOnBase.dual_of_isInvertible f hnτ hτ hsτ)
    exact E.trans (ofIso (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ whiskerLeftIso _ edτ)) h1
  ·
    have h2 : LocIsoOnBase f ((τ' ⊗ τ') ⊗ Scheme.Modules.dual (τ ⊗ τ)) (𝓛 ⊗ Scheme.Modules.dual 𝓛) :=
      LocIsoOnBase.tensor (E.symm sqτ') (LocIsoOnBase.dual_of_isInvertible f (hτ.tensor_monoidalV2 hτ) h𝓛 (E.symm sqτ))
    exact E.trans (ofIso (swapMiddle _ _ _ _ ≪≫ whiskerLeftIso _ eττ.symm)) (E.trans h2 (ofIso e𝓛))
  ·
    exact whiskerLeftIso τ (β_ τ' (Scheme.Modules.dual τ)) ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso eτ τ' ≪≫ λ_ τ'

end RootDiff

end

theorem solution
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    (𝓛 τ τ' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hτ : Scheme.Modules.IsInvertible τ) (hτ' : Scheme.Modules.IsInvertible τ')
    (hsτ : IsSymmetric f L τ) (hsτ' : IsSymmetric f L τ')
    (hrτ : LocIsoOnBase f 𝓛 (τ ⊗ (Scheme.Modules.pullback (negMor f L)).obj τ))
    (hrτ' : LocIsoOnBase f 𝓛 (τ' ⊗ (Scheme.Modules.pullback (negMor f L)).obj τ')) :
    IsSymmetric f L (τ' ⊗ Scheme.Modules.dual τ) ∧
      LocIsoOnBase f ((τ' ⊗ Scheme.Modules.dual τ) ⊗ (τ' ⊗ Scheme.Modules.dual τ)) (𝟙_ A.Modules) ∧
      Nonempty (τ ⊗ (τ' ⊗ Scheme.Modules.dual τ) ≅ τ') :=
  RootDiff.main L 𝓛 τ τ' h𝓛 hτ hτ' hsτ hsτ' hrτ hrτ'

end S_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_dual_of_isSymmetric_of_locIsoOnBase
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_dual_of_isSymmetric_of_locIsoOnBase (solution)
