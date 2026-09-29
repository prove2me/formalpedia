-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_phi_tensor_iso_phi_of_inPicZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/afef383d-c8b2-5ada-ab13-e283b39769fd

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_phi_tensor_iso_phi_of_inPicZero

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 M : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hM : InPicZero f L M) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Nonempty (
      (Scheme.Modules.pullback (L.translate x)).obj (𝓛 ⊗ M) ⊗ Scheme.Modules.dual (𝓛 ⊗ M) ≅
      (Scheme.Modules.pullback (L.translate x)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛) := by
  classical
  let Tx := L.translate x
  let X : A.Modules := (Scheme.Modules.pullback Tx).obj 𝓛
  let N : A.Modules := 𝓛 ⊗ M
  have hN : Scheme.Modules.IsInvertible N := Scheme.Modules.IsInvertible.tensor_monoidalV2 h𝓛 hM.1
  obtain ⟨U⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛).2
  obtain ⟨W⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hN).2
  obtain ⟨E⟩ := hM.2 x

  let J : Scheme.Modules.dual 𝓛 ≅ M ⊗ Scheme.Modules.dual N :=
    (ρ_ (Scheme.Modules.dual 𝓛)).symm ≪≫ (Iso.refl _ ⊗ᵢ W.symm) ≪≫
      (α_ (Scheme.Modules.dual 𝓛) N (Scheme.Modules.dual N)).symm ≪≫
      ((α_ (Scheme.Modules.dual 𝓛) 𝓛 M).symm ⊗ᵢ Iso.refl _) ≪≫
      (((β_ (Scheme.Modules.dual 𝓛) 𝓛 ≪≫ U) ⊗ᵢ Iso.refl M) ⊗ᵢ Iso.refl _) ≪≫
      ((λ_ M) ⊗ᵢ Iso.refl _)
  exact ⟨(Scheme.Modules.pullbackTensorObjIso Tx 𝓛 M ⊗ᵢ Iso.refl _) ≪≫ ((Iso.refl X ⊗ᵢ E) ⊗ᵢ Iso.refl _) ≪≫
    (α_ X M (Scheme.Modules.dual N)) ≪≫ (Iso.refl X ⊗ᵢ J.symm)⟩

end S_AlgebraicGeometry_Polarisation_nonempty_phi_tensor_iso_phi_of_inPicZero
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_phi_tensor_iso_phi_of_inPicZero (solution)
