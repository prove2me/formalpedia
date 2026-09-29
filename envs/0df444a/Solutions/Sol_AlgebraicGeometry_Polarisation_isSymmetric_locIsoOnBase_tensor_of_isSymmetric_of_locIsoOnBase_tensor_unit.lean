-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_tensor_of_isSymmetric_of_locIsoOnBase_tensor_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a1df9ad1-e938-5bb3-a20a-a8cc9e56cd38

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_of_isSymmetric_of_locIsoOnBase_tensor_unit

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace RootTwist

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem ofIso {M M' : A.Modules} (e : M ≅ M') : LocIsoOnBase f M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

def swapMiddle (a b c d : A.Modules) : (a ⊗ b) ⊗ (c ⊗ d) ≅ (a ⊗ c) ⊗ (b ⊗ d) :=
  α_ a b (c ⊗ d) ≪≫ whiskerLeftIso a ((α_ b c d).symm ≪≫ whiskerRightIso (β_ b c) d ≪≫ α_ c b d) ≪≫ (α_ a c (b ⊗ d)).symm

theorem main (L : RelativeGroupLaw R f)
    (𝓛 τ N : A.Modules)
    (hsτ : IsSymmetric f L τ) (hrτ : LocIsoOnBase f 𝓛 (τ ⊗ (Scheme.Modules.pullback (negMor f L)).obj τ))
    (hsN : IsSymmetric f L N) (h2N : LocIsoOnBase f (N ⊗ N) (𝟙_ A.Modules)) :
    IsSymmetric f L (τ ⊗ N) ∧ LocIsoOnBase f 𝓛 ((τ ⊗ N) ⊗ (Scheme.Modules.pullback (negMor f L)).obj (τ ⊗ N)) := by
  have E := LocIsoOnBase.equivalence f
  refine ⟨?_, ?_⟩
  · show LocIsoOnBase f ((Scheme.Modules.pullback (negMor f L)).obj (τ ⊗ N)) (τ ⊗ N)
    exact E.trans (ofIso (Scheme.Modules.pullbackTensorObjIso _ _ _)) (LocIsoOnBase.tensor hsτ hsN)
  · refine E.symm (E.trans (ofIso (whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso _ _ _) ≪≫ swapMiddle _ _ _ _)) ?_)
    exact E.trans (LocIsoOnBase.tensor (E.symm hrτ) (E.trans (LocIsoOnBase.tensor (E.refl N) hsN) h2N)) (ofIso (ρ_ 𝓛))

end RootTwist

end

theorem solution
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (𝓛 τ N : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hτ : Scheme.Modules.IsInvertible τ) (hN : Scheme.Modules.IsInvertible N)
    (hsτ : IsSymmetric f L τ) (hrτ : LocIsoOnBase f 𝓛 (τ ⊗ (Scheme.Modules.pullback (negMor f L)).obj τ))
    (hsN : IsSymmetric f L N) (h2N : LocIsoOnBase f (N ⊗ N) (𝟙_ A.Modules)) :
    IsSymmetric f L (τ ⊗ N) ∧ LocIsoOnBase f 𝓛 ((τ ⊗ N) ⊗ (Scheme.Modules.pullback (negMor f L)).obj (τ ⊗ N)) :=
  RootTwist.main L 𝓛 τ N hsτ hrτ hsN h2N

end S_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_of_isSymmetric_of_locIsoOnBase_tensor_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_of_isSymmetric_of_locIsoOnBase_tensor_unit (solution)
