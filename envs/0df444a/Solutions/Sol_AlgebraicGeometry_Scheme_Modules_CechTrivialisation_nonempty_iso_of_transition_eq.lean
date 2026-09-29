-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.CechTrivialisation.nonempty_iso_of_transition_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/19a7411f-b66f-5e64-a004-133529d21bb6

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_SheafOfModules_MonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_dual_forall_transition_mul_eq_one
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_tensor_forall_transition_eq_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_nonempty_iso_unit_of_forall_transition_eq_one
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_nonempty_iso_of_transition_eq
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace CategoryTheory.MonoidalCategory"

universe u

theorem solution
    {Y : Scheme.{u}} (𝒱 : Y.OrderedAffineCover) (𝓛 𝓛' : Y.Modules)
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓛) (τ' : Scheme.Modules.CechTrivialisation 𝒱 𝓛')
    (h : ∀ s : 𝒱.Idx 1, τ.transition s = τ'.transition s) :
    Nonempty (𝓛 ≅ 𝓛') := by

  have hinv' : Scheme.Modules.IsInvertible 𝓛' := ⟨fun y => by
    have hy : y ∈ (⨆ a, 𝒱.U a) := by rw [𝒱.iSup_eq_top]; trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hy
    exact ⟨𝒱.U a, ha, ⟨τ' a⟩⟩⟩

  obtain ⟨σ', hσ'⟩ :=
    AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_dual_forall_transition_mul_eq_one 𝒱 𝓛' τ'
  obtain ⟨σ, hσ⟩ :=
    AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_tensor_forall_transition_eq_mul 𝒱
      (Scheme.Modules.dual 𝓛') 𝓛 σ' τ
  have h1 : ∀ s : 𝒱.Idx 1, σ.transition s = 1 := fun s => by rw [hσ, h s, hσ']

  obtain ⟨e⟩ :=
    AlgebraicGeometry.Scheme.Modules.CechTrivialisation.nonempty_iso_unit_of_forall_transition_eq_one σ h1
  obtain ⟨d⟩ := (AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2 hinv').2

  exact ⟨(λ_ 𝓛).symm ≪≫ whiskerRightIso d.symm 𝓛 ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso 𝓛' e ≪≫ ρ_ 𝓛'⟩

end S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_nonempty_iso_of_transition_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_nonempty_iso_of_transition_eq (solution)
