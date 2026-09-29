-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.mem_kernelPts_iff_nonempty_pullback_sliceAt_mumfordBundle_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/476b4f87-50e1-51d2-8ce1-34d051c2d52e

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_sliceAt_mumfordBundle_iso_unit
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    x ∈ kernelPts f L 𝓛 ↔ Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) ≅ 𝟙_ ((pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules)) :=
  (AlgebraicGeometry.Polarisation.isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit
      k f L 𝓛 h𝓛 k (𝟙 (Spec (CommRingCat.of k))) x).trans
    (AlgebraicGeometry.Polarisation.locIsoOnBase_iff_nonempty_iso_of_field
      (pullback.snd f (𝟙 (Spec (CommRingCat.of k)))) _ _)

end S_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_sliceAt_mumfordBundle_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_sliceAt_mumfordBundle_iso_unit (solution)
