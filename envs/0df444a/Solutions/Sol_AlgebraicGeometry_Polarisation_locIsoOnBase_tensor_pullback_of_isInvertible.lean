-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.locIsoOnBase_tensor_pullback_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3643aae4-232b-5234-a225-b28d65135987

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_tensor_pullback_of_isInvertible

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Polarisation"

universe u

theorem solution
    {B : Type u} [CommRing B] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of B))
    (L : P.Modules) (N : (Spec (CommRingCat.of B)).Modules) (hN : Scheme.Modules.IsInvertible N) :
    LocIsoOnBase q (L ⊗ (Scheme.Modules.pullback q).obj N) L := by
  intro s
  obtain ⟨U, hsU, ⟨eU⟩⟩ := hN.exists_trivialization s
  refine ⟨U, hsU, ?_⟩

  have hfact : (q ⁻¹ᵁ U).ι ≫ q = (q ∣_ U) ≫ U.ι := (morphismRestrict_ι q U).symm
  have e : (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback q).obj N) ≅
      SheafOfModules.unit (q ⁻¹ᵁ U).toScheme.ringCatSheaf :=
    (Scheme.Modules.pullbackComp _ _).app N ≪≫
    (Scheme.Modules.pullbackCongr hfact).app N ≪≫
    ((Scheme.Modules.pullbackComp _ _).app N).symm ≪≫
    (Scheme.Modules.pullback (q ∣_ U)).mapIso eU ≪≫
    Scheme.Modules.pullbackUnitIso (q ∣_ U)
  exact ⟨AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso (q ⁻¹ᵁ U).ι L ((Scheme.Modules.pullback q).obj N) ≪≫
    whiskerLeftIso ((Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj L) e ≪≫ ρ_ _⟩

end S_AlgebraicGeometry_Polarisation_locIsoOnBase_tensor_pullback_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_tensor_pullback_of_isInvertible (solution)
