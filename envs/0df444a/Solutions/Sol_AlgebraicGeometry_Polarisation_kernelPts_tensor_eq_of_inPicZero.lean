-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.kernelPts_tensor_eq_of_inPicZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1e19c7fb-e701-5fdb-b8f8-7b0550b4118e

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_phi_tensor_iso_phi_of_inPicZero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_kernelPts_tensor_eq_of_inPicZero
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace KptsTwistBody

variable {X : Scheme.{0}}

theorem tensor_dual_iso_unit_of_iso {N P : X.Modules} (hP : Scheme.Modules.IsInvertible P)
    (h : Nonempty (N ≅ P)) : Nonempty (N ⊗ Scheme.Modules.dual P ≅ 𝟙_ X.Modules) := by
  obtain ⟨e⟩ := h
  obtain ⟨ε⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hP).2
  exact ⟨(e ⊗ᵢ Iso.refl _) ≪≫ ε⟩

theorem iso_of_tensor_dual_iso_unit {N P : X.Modules} (hP : Scheme.Modules.IsInvertible P)
    (h : Nonempty (N ⊗ Scheme.Modules.dual P ≅ 𝟙_ X.Modules)) : Nonempty (N ≅ P) := by
  obtain ⟨e⟩ := h
  obtain ⟨ε⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hP).2
  exact CategoryTheory.MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit
    (Iso.refl (Scheme.Modules.dual P)) ⟨(β_ _ _) ≪≫ e⟩ ⟨(β_ _ _) ≪≫ ε⟩

end KptsTwistBody

open KptsTwistBody in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (Q : A.Modules) (hQ : InPicZero f L Q) :
    kernelPts f L (𝓜 ⊗ Q) = kernelPts f L 𝓜 := by
  ext x
  rw [AlgebraicGeometry.Polarisation.mem_kernelPts_iff_nonempty_pullback_translate_iso,
    AlgebraicGeometry.Polarisation.mem_kernelPts_iff_nonempty_pullback_translate_iso]
  have hMQ : Scheme.Modules.IsInvertible (𝓜 ⊗ Q) :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_monoidalV2 h𝓜 hQ.1
  obtain ⟨Φ⟩ := AlgebraicGeometry.Polarisation.nonempty_phi_tensor_iso_phi_of_inPicZero k f L 𝓜 Q h𝓜 hQ x
  constructor
  · intro h
    obtain ⟨u⟩ := tensor_dual_iso_unit_of_iso hMQ h
    exact iso_of_tensor_dual_iso_unit h𝓜 ⟨Φ.symm ≪≫ u⟩
  · intro h
    obtain ⟨u⟩ := tensor_dual_iso_unit_of_iso h𝓜 h
    exact iso_of_tensor_dual_iso_unit hMQ ⟨Φ ≪≫ u⟩

end S_AlgebraicGeometry_Polarisation_kernelPts_tensor_eq_of_inPicZero
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_kernelPts_tensor_eq_of_inPicZero (solution)
