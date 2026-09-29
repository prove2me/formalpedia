-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_tensor_pullback_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/725de2e4-b151-5546-95c4-30f82bf01c6d

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_pullback_of_isInvertible

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace RootTwist

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem ofIso {M M' : A.Modules} (e : M ≅ M') : LocIsoOnBase f M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

def swapMiddle (a b c d : A.Modules) : (a ⊗ b) ⊗ (c ⊗ d) ≅ (a ⊗ c) ⊗ (b ⊗ d) :=
  α_ a b (c ⊗ d) ≪≫ whiskerLeftIso a ((α_ b c d).symm ≪≫ whiskerRightIso (β_ b c) d ≪≫ α_ c b d) ≪≫ (α_ a c (b ⊗ d)).symm

private theorem _root_.RootTwist.main (L : RelativeGroupLaw R f)
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

p2m_export "RootTwist" "main"
end RootTwist

namespace BaseTwist

variable {R : Type} [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R))

theorem locIsoOnBase_pullback_unit (E : (Spec (CommRingCat.of R)).Modules) (hE : Scheme.Modules.IsInvertible E) :
    LocIsoOnBase f ((Scheme.Modules.pullback f).obj E) (𝟙_ A.Modules) := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := hE.1 s
  refine ⟨U, hs, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp _ _).app E ≪≫ (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app E ≪≫
    ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app E).symm ≪≫ (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (f ∣_ U) ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso (f ⁻¹ᵁ U).ι).symm

private theorem _root_.BaseTwist.main (L : RelativeGroupLaw R f)
    (𝓛 τ : A.Modules) (D : (Spec (CommRingCat.of R)).Modules) (hD : Scheme.Modules.IsInvertible D)
    (hsτ : IsSymmetric f L τ) (hrτ : LocIsoOnBase f 𝓛 (τ ⊗ (Scheme.Modules.pullback (negMor f L)).obj τ)) :
    IsSymmetric f L (τ ⊗ (Scheme.Modules.pullback f).obj D) ∧
      LocIsoOnBase f 𝓛 ((τ ⊗ (Scheme.Modules.pullback f).obj D) ⊗
        (Scheme.Modules.pullback (negMor f L)).obj (τ ⊗ (Scheme.Modules.pullback f).obj D)) := by
  have E := LocIsoOnBase.equivalence f
  have hsN : IsSymmetric f L ((Scheme.Modules.pullback f).obj D) :=
    RootTwist.ofIso ((Scheme.Modules.pullbackComp (negMor f L) f).app D ≪≫ (Scheme.Modules.pullbackCongr (negMor_over f L)).app D)
  have h2N : LocIsoOnBase f ((Scheme.Modules.pullback f).obj D ⊗ (Scheme.Modules.pullback f).obj D) (𝟙_ A.Modules) :=
    E.trans (RootTwist.ofIso (Scheme.Modules.pullbackTensorObjIso f D D).symm)
      (locIsoOnBase_pullback_unit f (D ⊗ D) (hD.tensor_monoidalV2 hD))
  exact RootTwist.main L 𝓛 τ _ hsτ hrτ hsN h2N

p2m_export "BaseTwist" "main"
end BaseTwist

end

theorem solution
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (𝓛 τ : A.Modules) (D : (Spec (CommRingCat.of R)).Modules) (hD : Scheme.Modules.IsInvertible D)
    (hsτ : IsSymmetric f L τ) (hrτ : LocIsoOnBase f 𝓛 (τ ⊗ (Scheme.Modules.pullback (negMor f L)).obj τ)) :
    IsSymmetric f L (τ ⊗ (Scheme.Modules.pullback f).obj D) ∧
      LocIsoOnBase f 𝓛 ((τ ⊗ (Scheme.Modules.pullback f).obj D) ⊗
        (Scheme.Modules.pullback (negMor f L)).obj (τ ⊗ (Scheme.Modules.pullback f).obj D)) :=
  BaseTwist.main f L 𝓛 τ D hD hsτ hrτ

end S_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_pullback_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_pullback_of_isInvertible (solution)
