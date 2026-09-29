-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_det_succ_iso_det_tensor_of_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/86e07ade-2207-5dec-979a-8fa874371c15

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesWedge
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_locallySurjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_det_succ_iso_det_tensor_of_shortExact
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory"

set_option autoImplicit false

theorem solution
    {X : Scheme.{u}} {n : ℕ} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : Scheme.Modules.IsLocallyFreeOfRank n S.X₁) (h₂ : Scheme.Modules.IsLocallyFreeOfRank (n + 1) S.X₂)
    (h₃ : Scheme.Modules.IsInvertible S.X₃) :
    Nonempty (Scheme.Modules.det (n + 1) S.X₂ ≅ Scheme.Modules.det n S.X₁ ⊗ S.X₃) := by
  haveI := hS.epi_g

  let D : X.Modules := Scheme.Modules.det n S.X₁
  let ψ : D ⊗ S.X₂ ⟶ Scheme.Modules.det (n + 1) S.X₂ :=
    ((Scheme.Modules.exteriorPower X n).map S.f ▷ S.X₂) ≫ Scheme.Modules.wedgeVec n S.X₂

  have hzero : (D ◁ S.f) ≫ ψ = 0 := by
    have hnat : (D ◁ S.f) ≫ ψ =
        Scheme.Modules.wedgeVec n S.X₁ ≫ (Scheme.Modules.exteriorPower X (n + 1)).map S.f := by
      simp only [ψ, D, ← Category.assoc, ← MonoidalCategory.tensorHom_def',
        Scheme.Modules.wedgeVec_naturality]
    have hZ := AlgebraicGeometry.Scheme.Modules.isZero_exteriorPower_of_isLocallyFreeOfRank h₁ (Nat.lt_succ_self n)
    rw [hnat, hZ.eq_of_tgt (Scheme.Modules.wedgeVec n S.X₁) 0, zero_comp]

  let G : X.Modules ⥤ X.Modules := tensorLeft D
  have hGf : G.map S.f = D ◁ S.f := rfl
  let hc : IsColimit (CokernelCofork.ofπ (G.map (cokernel.π S.f))
      (show G.map S.f ≫ G.map (cokernel.π S.f) = 0 by rw [← G.map_comp, cokernel.condition, G.map_zero]) :
        CokernelCofork (G.map S.f)) :=
    isColimitOfHasCokernelOfPreservesColimit G S.f

  let φ' : G.obj (cokernel S.f) ⟶ Scheme.Modules.det (n + 1) S.X₂ :=
    hc.desc (CokernelCofork.ofπ ψ (by rw [hGf]; exact hzero))
  have hφ' : G.map (cokernel.π S.f) ≫ φ' = ψ := hc.fac _ WalkingParallelPair.one

  let e₃ := IsColimit.coconePointUniqueUpToIso hS.exact.gIsCokernel (cokernelIsCokernel S.f)
  have he₃ : S.g ≫ e₃.hom = cokernel.π S.f := by
    simpa using IsColimit.comp_coconePointUniqueUpToIso_hom hS.exact.gIsCokernel (cokernelIsCokernel S.f)
      WalkingParallelPair.one
  let φ : D ⊗ S.X₃ ⟶ Scheme.Modules.det (n + 1) S.X₂ := (D ◁ e₃.hom) ≫ φ'
  have hfac : (D ◁ S.g) ≫ φ = ψ := by
    simp only [φ, ← MonoidalCategory.whiskerLeft_comp_assoc, he₃]
    exact hφ'

  haveI hψ : Epi ψ := AlgebraicGeometry.Scheme.Modules.epi_whiskerRight_wedgeVec_of_shortExact S hS h₁ h₃
  haveI : Epi φ := epi_of_epi_fac hfac
  have hDL : Scheme.Modules.IsInvertible (D ⊗ S.X₃) :=
    (AlgebraicGeometry.Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank h₁).tensor h₃
  have hE : Scheme.Modules.IsInvertible (Scheme.Modules.det (n + 1) S.X₂) :=
    AlgebraicGeometry.Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank h₂
  haveI : IsIso φ := AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_locallySurjective hDL hE φ
    ((AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective φ).mp inferInstance)
  exact ⟨(asIso φ).symm⟩

end S_AlgebraicGeometry_Scheme_Modules_nonempty_det_succ_iso_det_tensor_of_shortExact
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_det_succ_iso_det_tensor_of_shortExact (solution)
