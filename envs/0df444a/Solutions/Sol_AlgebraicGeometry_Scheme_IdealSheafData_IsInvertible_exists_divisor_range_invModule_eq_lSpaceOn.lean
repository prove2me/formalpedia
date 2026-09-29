-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_divisor_range_invModule_eq_lSpaceOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7e2aef92-4fa7-5221-b840-e959863444e3

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import Theorems.Thm_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_invModule_eq_lSpaceOn
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

universe u

set_option maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_invModule_eq_lSpaceOn.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Hom Scheme.germToFunctionField_injective Scheme.Opens.ι_appIso Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact Spec IsIntegral Scheme.Modules.mapPresheaf_app Scheme Scheme.Hom.appIso Scheme.Opens.topIso_hom Scheme.Hom.preimage_mono IsSeparated IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.toUnitSection Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible.exists_restrict_iso Scheme.IdealSheafData.IsInvertible Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul germToFunctionField ringCatSheaf Hom.id_app Hom germToFunctionField_injective Γ Opens.ι_appIso topIso_hom Modules.Hom Hom.image_preimage_eq_opensRange_inf topIso Modules.mapPresheaf_app Hom.appIso functionField Opens.topIso_hom Hom.preimage_mono affineBasicOpen affineOpens Hom.comp_app isBasis_affineOpens Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict IdealSheafData Modules.IsInvertible Modules.toUnitSection Modules.zeroSchemeIdeal Modules.IsInvertible.exists_restrict_iso IdealSheafData.IsInvertible Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app restrict_map isSheaf restrict map_smul IsInvertible toUnitSection ofUnitSection ofUnitSection_toUnitSection ofUnitSection_injective ofUnitSection_map coeff zeroSchemeIdeal IsInvertible.exists_restrict_iso IsInvertible.exists_divisor_range_eq_lSpaceOn IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq"
namespace RatSec
p2m_open "AlgebraicGeometry.Scheme.Modules~restrict_smul_eq AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}} (M : X.Modules)

noncomputable abbrev rM {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) := fun y => M.presheaf.map (homOfLE h).op y

noncomputable abbrev rO {V W : X.Opens} (h : V ≤ W) : Γ(X, W) → Γ(X, V) := fun g => X.presheaf.map (homOfLE h).op g

theorem rM_rM {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    rM M h₃₂ (rM M h₂₁ y) = rM M (h₃₂.trans h₂₁) y := by
  show (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

omit M in
theorem rO_rO {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (g : Γ(X, V₁)) :
    rO h₃₂ (rO h₂₁ g) = rO (h₃₂.trans h₂₁) g := by
  show (X.presheaf.map (homOfLE h₂₁).op ≫ X.presheaf.map (homOfLE h₃₂).op).hom g = _
  rw [← Functor.map_comp]; rfl

theorem rM_self {V : X.Opens} (h : V ≤ V) (y : Γ(M, V)) : rM M h y = y := by
  show (M.presheaf.map (homOfLE h).op) y = y
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, M.presheaf.map_id]; rfl

omit M in
theorem rO_self {V : X.Opens} (h : V ≤ V) (g : Γ(X, V)) : rO h g = g := by
  show (X.presheaf.map (homOfLE h).op).hom g = g
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, X.presheaf.map_id]; rfl

theorem rM_smul {V W : X.Opens} (h : V ≤ W) (g : Γ(X, W)) (y : Γ(M, W)) :
    rM M h (g • y) = rO h g • rM M h y := M.map_smul _ _ _

theorem rM_add {V W : X.Opens} (h : V ≤ W) (y y' : Γ(M, W)) :
    rM M h (y + y') = rM M h y + rM M h y' := map_add _ _ _

theorem rM_zero {V W : X.Opens} (h : V ≤ W) : rM M h (0 : Γ(M, W)) = 0 := map_zero _

theorem rM_sub {V W : X.Opens} (h : V ≤ W) (y y' : Γ(M, W)) :
    rM M h (y - y') = rM M h y - rM M h y' := map_sub _ _ _

omit M in
theorem rO_one {V W : X.Opens} (h : V ≤ W) : rO h (1 : Γ(X, W)) = 1 := map_one _

omit M in
theorem rO_mul {V W : X.Opens} (h : V ≤ W) (a b : Γ(X, W)) : rO h (a * b) = rO h a * rO h b := map_mul _ _ _

omit M in
theorem rO_zero {V W : X.Opens} (h : V ≤ W) : rO h (0 : Γ(X, W)) = 0 := map_zero _

section Transport

variable (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

theorem hat_eq {W : X.Opens} (hWV : W ≤ V) : V.ι ''ᵁ V.ι ⁻¹ᵁ W = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWV]

theorem le_hat {W : X.Opens} (hWV : W ≤ V) : W ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ W := (hat_eq V hWV).ge
theorem hat_le {W : X.Opens} (hWV : W ≤ V) : V.ι ''ᵁ V.ι ⁻¹ᵁ W ≤ W := (hat_eq V hWV).le

noncomputable def eApp (W : X.Opens) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W) :=
  (e.hom.app (V.ι ⁻¹ᵁ W)).hom m

noncomputable def eInv (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W) :=
  (e.inv.app (V.ι ⁻¹ᵁ W)).hom a

theorem eInv_eApp (W : X.Opens) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : eInv M V e W (eApp M V e W m) = m := by
  show (e.hom.app (V.ι ⁻¹ᵁ W) ≫ e.inv.app (V.ι ⁻¹ᵁ W)).hom m = m
  rw [← Hom.comp_app, e.hom_inv_id, Hom.id_app]; rfl

theorem eApp_eInv (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : eApp M V e W (eInv M V e W a) = a := by
  show (e.inv.app (V.ι ⁻¹ᵁ W) ≫ e.hom.app (V.ι ⁻¹ᵁ W)).hom a = a
  rw [← Hom.comp_app, e.inv_hom_id, Hom.id_app]; rfl

theorem eApp_zero (W : X.Opens) : eApp M V e W 0 = 0 := (e.hom.app (V.ι ⁻¹ᵁ W)).hom.map_zero

theorem eApp_add (W : X.Opens) (m m' : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    eApp M V e W (m + m') = eApp M V e W m + eApp M V e W m' := (e.hom.app (V.ι ⁻¹ᵁ W)).hom.map_add m m'

theorem eApp_injective (W : X.Opens) : Function.Injective (eApp M V e W) :=
  Function.LeftInverse.injective (eInv_eApp M V e W)

theorem restrict_smul_eq (W' : V.toScheme.Opens) (b : Γ(V.toScheme, W')) (m : Γ(M.restrict V.ι, W')) :
    (HSMul.hSMul (α := Γ(V.toScheme, W')) (β := Γ(M.restrict V.ι, W')) b m : Γ(M, V.ι ''ᵁ W'))
      = HSMul.hSMul (α := Γ(X, V.ι ''ᵁ W')) (β := Γ(M, V.ι ''ᵁ W')) ((Scheme.Hom.appIso V.ι W').inv b) m := rfl

theorem eApp_smul (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    eApp M V e W (a • m) = a * eApp M V e W m := by
  have hinv : (Scheme.Hom.appIso V.ι (V.ι ⁻¹ᵁ W)).inv a = a := by
    rw [Scheme.Opens.ι_appIso]; rfl
  have h := Hom.app_smul e.hom (U := V.ι ⁻¹ᵁ W) a m
  have hl := restrict_smul_eq M V (V.ι ⁻¹ᵁ W) a m
  rw [hinv] at hl
  unfold eApp
  rw [← hl]
  exact h.trans rfl

theorem eApp_res {W₁ W₂ : X.Opens} (h : W₂ ≤ W₁) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W₁)) :
    eApp M V e W₂ (rM M (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) m)
      = rO (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) (eApp M V e W₁ m) := by
  have hnat := e.hom.mapPresheaf.naturality (homOfLE (Scheme.Hom.preimage_mono V.ι h)).op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hx
  have e1 : (Scheme.Hom.opensFunctor V.ι).map (homOfLE (Scheme.Hom.preimage_mono V.ι h))
      = homOfLE (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) := Subsingleton.elim _ _
  rw [restrict_map, e1] at hx
  exact hx

noncomputable def ψ {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : Γ(X, W) :=
  rO (le_hat V hWV) (eApp M V e W (rM M (hat_le V hWV) m))

noncomputable def ψinv {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : Γ(M, W) :=
  rM M (le_hat V hWV) (eInv M V e W (rO (hat_le V hWV) a))

theorem rM_roundtrip {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : rM M (le_hat V hWV) (rM M (hat_le V hWV) m) = m := by
  rw [rM_rM, rM_self]
theorem rM_roundtrip' {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    rM M (hat_le V hWV) (rM M (le_hat V hWV) m) = m := by
  rw [rM_rM, rM_self]
omit M e in
theorem rO_roundtrip {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : rO (le_hat V hWV) (rO (hat_le V hWV) a) = a := by
  rw [rO_rO, rO_self]
omit M e in
theorem rO_roundtrip' {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    rO (hat_le V hWV) (rO (le_hat V hWV) a) = a := by
  rw [rO_rO, rO_self]

theorem ψ_ψinv {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : ψ M V e hWV (ψinv M V e hWV a) = a := by
  simp only [ψ, ψinv]
  rw [rM_roundtrip' M V hWV, eApp_eInv, rO_roundtrip V hWV]

theorem ψinv_ψ {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : ψinv M V e hWV (ψ M V e hWV m) = m := by
  simp only [ψ, ψinv]
  rw [rO_roundtrip' V hWV, eInv_eApp, rM_roundtrip M V hWV]

theorem ψ_injective {W : X.Opens} (hWV : W ≤ V) : Function.Injective (ψ M V e hWV) :=
  Function.LeftInverse.injective (ψinv_ψ M V e hWV)

theorem ψ_zero {W : X.Opens} (hWV : W ≤ V) : ψ M V e hWV 0 = 0 := by
  simp only [ψ]
  show rO (le_hat V hWV) (eApp M V e W ((M.presheaf.map _) 0)) = 0
  rw [map_zero, eApp_zero]; exact map_zero _

theorem ψ_add {W : X.Opens} (hWV : W ≤ V) (m m' : Γ(M, W)) :
    ψ M V e hWV (m + m') = ψ M V e hWV m + ψ M V e hWV m' := by
  simp only [ψ]
  rw [rM_add, eApp_add]
  exact map_add _ _ _

theorem ψ_smul {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) (m : Γ(M, W)) :
    ψ M V e hWV (a • m) = a * ψ M V e hWV m := by
  simp only [ψ]
  rw [rM_smul, eApp_smul]
  show (X.presheaf.map _).hom (_ * _) = a * _
  rw [map_mul]
  congr 1
  exact rO_roundtrip V hWV a

theorem ψ_res {W₁ W₂ : X.Opens} (h₁ : W₁ ≤ V) (h : W₂ ≤ W₁) (m : Γ(M, W₁)) :
    ψ M V e (h.trans h₁) (rM M h m) = rO h (ψ M V e h₁ m) := by
  simp only [ψ]
  have lhs : rM M (hat_le V (h.trans h₁)) (rM M h m)
      = rM M (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) (rM M (hat_le V h₁) m) := by
    rw [rM_rM, rM_rM]
  rw [lhs, eApp_res M V e h, rO_rO, rO_rO]

noncomputable def frame : Γ(M, V) := ψinv M V e le_rfl 1

theorem ψ_frame : ψ M V e le_rfl (frame M V e) = 1 := ψ_ψinv M V e le_rfl 1

theorem ψ_rM_frame {W : X.Opens} (hWV : W ≤ V) : ψ M V e hWV (rM M hWV (frame M V e)) = 1 := by
  have h := ψ_res M V e le_rfl hWV (frame M V e)
  rw [ψ_frame, rO_one] at h
  exact h

theorem eq_smul_frame {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) :
    m = ψ M V e hWV m • rM M hWV (frame M V e) := by
  apply ψ_injective M V e hWV
  rw [ψ_smul, ψ_rM_frame, mul_one]

end Transport

section Integral

variable [IsIntegral X]

omit M in
theorem nonempty_inf (U W : X.Opens) [hU : Nonempty U] [hW : Nonempty W] : Nonempty (U ⊓ W : X.Opens) := by
  obtain ⟨⟨u, hu⟩⟩ := hU
  obtain ⟨⟨w, hw⟩⟩ := hW
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen ⟨u, hu⟩ ⟨w, hw⟩
  exact ⟨⟨z, hz⟩⟩

omit M in

noncomputable abbrev alg (U : X.Opens) [Nonempty U] (a : Γ(X, U)) : X.functionField :=
  (X.germToFunctionField U).hom a

omit M in
theorem alg_rO {U W : X.Opens} [Nonempty U] [Nonempty W] (h : W ≤ U) (a : Γ(X, U)) :
    alg W (rO h a) = alg U a := by
  show (X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField W).hom a = _
  unfold Scheme.germToFunctionField
  rw [TopCat.Presheaf.germ_res]

omit M in
theorem alg_injective (U : X.Opens) [Nonempty U] : Function.Injective (alg (X := X) U) :=
  Scheme.germToFunctionField_injective X U

omit M in
theorem rO_injective {U W : X.Opens} [Nonempty U] [Nonempty W] (h : W ≤ U) :
    Function.Injective (rO (X := X) h) := by
  intro a b hab
  apply alg_injective U
  rw [← alg_rO h, ← alg_rO h, hab]

omit M in
theorem alg_one (U : X.Opens) [Nonempty U] : alg U (1 : Γ(X, U)) = 1 := map_one _

omit M in
theorem alg_zero (U : X.Opens) [Nonempty U] : alg U (0 : Γ(X, U)) = 0 := map_zero _

omit M in
theorem alg_add (U : X.Opens) [Nonempty U] (a b : Γ(X, U)) : alg U (a + b) = alg U a + alg U b := map_add _ _ _

omit M in
theorem alg_mul (U : X.Opens) [Nonempty U] (a b : Γ(X, U)) : alg U (a * b) = alg U a * alg U b := map_mul _ _ _

end Integral

section Places

open AlgebraicCurve WithZero

variable {K : Type u} [Field K] (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [SmoothOfRelativeDimension 1 x]

omit M in

theorem adicValuation_alg_le_one (W : X.Opens) (y : X) (hyW : y ∈ W) (hy : IsClosed ({y} : Set X))
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring)
    (a : Γ(X, W)) :
    letI := (baseToFunctionField x).toAlgebra
    haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
    v.adicValuation (alg W a) ≤ 1 := by
  letI := (baseToFunctionField x).toAlgebra
  haveI : Nonempty W := ⟨⟨y, hyW⟩⟩

  obtain ⟨W', hW'aff, hyW', hW'W⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hyW
  haveI : Nonempty W' := ⟨⟨y, hyW'⟩⟩
  rw [← alg_rO hW'W a]
  apply (Place.mem_iff_adicValuation_le_one v).mp
  have hmem : alg W' (rO hW'W a) ∈ (algebraMap Γ(X, W') X.functionField).range := ⟨rO hW'W a, rfl⟩
  rw [range_algebraMap_functionField_eq_iInf_of_isAffineOpen x W' hW'aff] at hmem
  have h2 := (Subring.mem_iInf.mp hmem) v
  have h3 := (Subring.mem_iInf.mp h2) ⟨y, hyW', hy, hv⟩
  exact h3

def IsGeneratorAt (U : X.Opens) (s : Γ(M, U)) (y : X) : Prop :=
  ∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(M, W), ∃ a : Γ(X, W), m = a • rM M h s

omit x [IsIntegral X] in
theorem isGeneratorAt_frame (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
    (y : X) : IsGeneratorAt M V (frame M V e) y :=
  fun _ h _ m => ⟨ψ M V e h m, eq_smul_frame M V e h m⟩

omit x [IsIntegral X] in
theorem isGeneratorAt_rM {U W : X.Opens} (h : W ≤ U) (s : Γ(M, U)) (y : X) (hs : IsGeneratorAt M U s y) :
    IsGeneratorAt M W (rM M h s) y := by
  intro W' h' hyW' m
  obtain ⟨a, ha⟩ := hs W' (h'.trans h) hyW' m
  exact ⟨a, by rw [rM_rM]; exact ha⟩

end Places

end AlgebraicGeometry.Scheme.Modules.RatSec

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Hom Scheme.germToFunctionField_injective Scheme.Opens.ι_appIso Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact Spec IsIntegral Scheme.Modules.mapPresheaf_app Scheme Scheme.Hom.appIso Scheme.Opens.topIso_hom Scheme.Hom.preimage_mono IsSeparated IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.toUnitSection Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible.exists_restrict_iso Scheme.IdealSheafData.IsInvertible Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul germToFunctionField ringCatSheaf Hom.id_app Hom germToFunctionField_injective Γ Opens.ι_appIso topIso_hom Modules.Hom Hom.image_preimage_eq_opensRange_inf topIso Modules.mapPresheaf_app Hom.appIso functionField Opens.topIso_hom Hom.preimage_mono affineBasicOpen affineOpens Hom.comp_app isBasis_affineOpens Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict IdealSheafData Modules.IsInvertible Modules.toUnitSection Modules.zeroSchemeIdeal Modules.IsInvertible.exists_restrict_iso IdealSheafData.IsInvertible Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "map map_id ideal map_comp map_ideal module moduleι invModule invModuleSection IsInvertible range_moduleIota_app_and_injective IsInvertible.isInvertible_invModule"
namespace PresMod
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.Modules~restrict_smul_eq P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_invModule_eq_lSpaceOn.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_invModule_eq_lSpaceOn.AlgebraicGeometry.Scheme.Modules.RatSec AlgebraicCurve WithZero"

variable {X : Scheme.{u}} (I : X.IdealSheafData)

noncomputable def fn (U : X.Opens) (m : Γ(I.module, U)) : Γ(X, U) :=
  ofUnitSection U (I.moduleι.app U m)

theorem fn_add (U : X.Opens) (m m' : Γ(I.module, U)) : fn I U (m + m') = fn I U m + fn I U m' := by
  simp only [fn, map_add]; rfl

theorem fn_zero (U : X.Opens) : fn I U (0 : Γ(I.module, U)) = 0 := by
  simp only [fn, map_zero]; rfl

theorem fn_sub (U : X.Opens) (m m' : Γ(I.module, U)) : fn I U (m - m') = fn I U m - fn I U m' := by
  simp only [fn, map_sub]; rfl

theorem fn_smul (U : X.Opens) (a : Γ(X, U)) (m : Γ(I.module, U)) : fn I U (a • m) = a * fn I U m := by
  simp only [fn, Scheme.Modules.Hom.app_smul]; rfl

theorem fn_rM {U W : X.Opens} (h : W ≤ U) (m : Γ(I.module, U)) :
    fn I W (rM I.module h m) = rO h (fn I U m) := by
  simp only [fn, rM, rO]
  have nat := (I.moduleι.mapPresheaf).naturality (homOfLE h).op
  have hx := congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(I.module, U) → Γ(𝟙_ X.Modules, W))) nat) m
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hx

  rw [hx]
  rfl

theorem fn_injective_affine (U : X.Opens) (hU : IsAffineOpen U) : Function.Injective (fn I U) := by
  intro m m' h
  exact (range_moduleIota_app_and_injective I ⟨U, hU⟩).2 (ofUnitSection_injective U h)

theorem range_fn_affine (U : X.Opens) (hU : IsAffineOpen U) :
    Set.range (fn I U) = (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) := by
  have h := (range_moduleIota_app_and_injective I ⟨U, hU⟩).1
  ext g
  constructor
  · rintro ⟨m, rfl⟩
    have hm : (I.moduleι.app U m : Γ(𝟙_ X.Modules, U)) ∈ Set.range (I.moduleι.app (⟨U, hU⟩ : X.affineOpens)) := ⟨m, rfl⟩
    rw [h] at hm
    exact hm
  · intro hg
    have hg' : (toUnitSection U g) ∈ Set.range (I.moduleι.app (⟨U, hU⟩ : X.affineOpens)) := by rw [h]; exact hg
    obtain ⟨m, hm⟩ := hg'
    refine ⟨m, ?_⟩
    simp only [fn]
    rw [hm]
    rfl

theorem fn_injective (U : X.Opens) : Function.Injective (fn I U) := by
  intro m m' hmm
  rw [← sub_eq_zero] at hmm ⊢
  rw [← fn_sub] at hmm
  set n := m - m' with hn
  clear_value n
  clear hn m m'

  have hloc : ∀ (W : X.Opens) (hW : IsAffineOpen W) (h : W ≤ U), rM I.module h n = 0 := by
    intro W hW h
    apply fn_injective_affine I W hW
    rw [fn_rM, hmm, fn_zero, rO_zero]

  let F : TopCat.Sheaf Ab X := ⟨I.module.presheaf, I.module.isSheaf⟩
  have hcov : ∀ z : U, ∃ W : X.Opens, IsAffineOpen W ∧ (z : X) ∈ W ∧ W ≤ U := by
    intro z
    obtain ⟨W, hWaff, hzW, hWU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) z.2
    exact ⟨W, hWaff, hzW, hWU⟩
  choose W hWaff hzW hWU using hcov
  refine TopCat.Sheaf.eq_of_locally_eq' F W U (fun z => homOfLE (hWU z)) ?_ n 0 ?_
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hzW ⟨y, hy⟩⟩
  · intro z
    have := hloc (W z) (hWaff z) (hWU z)
    simp only [rM] at this
    rw [map_zero]
    exact this

section Curve

variable {K : Type u} [Field K] (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [SmoothOfRelativeDimension 1 x]

omit x [IsIntegral X] [SmoothOfRelativeDimension 1 x] in

theorem frame_ne_zero (V : X.Opens) [Nonempty V]
    (e : I.module.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) : frame I.module V e ≠ 0 := by
  intro h
  have h1 := ψ_frame I.module V e
  rw [h, ψ_zero] at h1
  exact zero_ne_one h1

theorem adicValuation_alg_eq_of_span_eq (W : X.Opens) (y : X) (hyW : y ∈ W) (hy : IsClosed ({y} : Set X))
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring)
    (g g' : Γ(X, W)) (hgg' : Ideal.span {g} = Ideal.span {g'}) :
    letI := (baseToFunctionField x).toAlgebra
    haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
    v.adicValuation (alg W g) = v.adicValuation (alg W g') := by
  letI := (baseToFunctionField x).toAlgebra
  haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
  have h1 : g ∈ Ideal.span {g'} := hgg' ▸ Ideal.mem_span_singleton_self g
  have h2 : g' ∈ Ideal.span {g} := hgg'.symm ▸ Ideal.mem_span_singleton_self g'
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h2
  apply le_antisymm
  · rw [← ha, alg_mul, Valuation.map_mul]
    calc v.adicValuation (alg W a) * v.adicValuation (alg W g')
        ≤ 1 * v.adicValuation (alg W g') :=
          mul_le_mul_left (adicValuation_alg_le_one x W y hyW hy v hv a) _
      _ = v.adicValuation (alg W g') := one_mul _
  · rw [← hb, alg_mul, Valuation.map_mul]
    calc v.adicValuation (alg W b) * v.adicValuation (alg W g)
        ≤ 1 * v.adicValuation (alg W g) :=
          mul_le_mul_left (adicValuation_alg_le_one x W y hyW hy v hv b) _
      _ = v.adicValuation (alg W g) := one_mul _

end Curve

end AlgebraicGeometry.Scheme.IdealSheafData.PresMod

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Hom Scheme.germToFunctionField_injective Scheme.Opens.ι_appIso Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact Spec IsIntegral Scheme.Modules.mapPresheaf_app Scheme Scheme.Hom.appIso Scheme.Opens.topIso_hom Scheme.Hom.preimage_mono IsSeparated IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.toUnitSection Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible.exists_restrict_iso Scheme.IdealSheafData.IsInvertible Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul germToFunctionField ringCatSheaf Hom.id_app Hom germToFunctionField_injective Γ Opens.ι_appIso topIso_hom Modules.Hom Hom.image_preimage_eq_opensRange_inf topIso Modules.mapPresheaf_app Hom.appIso functionField Opens.topIso_hom Hom.preimage_mono affineBasicOpen affineOpens Hom.comp_app isBasis_affineOpens Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict IdealSheafData Modules.IsInvertible Modules.toUnitSection Modules.zeroSchemeIdeal Modules.IsInvertible.exists_restrict_iso IdealSheafData.IsInvertible Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app restrict_map isSheaf restrict map_smul IsInvertible toUnitSection ofUnitSection ofUnitSection_toUnitSection ofUnitSection_injective ofUnitSection_map coeff zeroSchemeIdeal IsInvertible.exists_restrict_iso IsInvertible.exists_divisor_range_eq_lSpaceOn IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq"
namespace RatSec
p2m_open "AlgebraicGeometry.Scheme.Modules~restrict_smul_eq AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory.MonoidalCategory"

section Coeff

variable {X : Scheme.{u}} (M : X.Modules) (V : X.Opens)
  (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) (σ : 𝟙_ X.Modules ⟶ M)

theorem rM_section_one {U W : X.Opens} (h : W ≤ U) :
    rM M h (σ.app U (toUnitSection U 1)) = σ.app W (toUnitSection W 1) := by
  simp only [rM]
  have nat := (σ.mapPresheaf).naturality (homOfLE h).op
  have hx := congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(𝟙_ X.Modules, U) → Γ(M, W))) nat)
    (toUnitSection U 1)
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hx
  rw [← hx]
  congr 1
  apply ofUnitSection_injective
  rw [ofUnitSection_map, ofUnitSection_toUnitSection, ofUnitSection_toUnitSection, map_one]

theorem ψ_section_eq_coeff :
    ψ M V e le_rfl (σ.app V (toUnitSection V 1)) = coeff σ V e.hom := by

  let i₁ : (V.ι ⁻¹ᵁ V : V.toScheme.Opens) ⟶ ⊤ := homOfLE le_top
  have hj : V.ι ''ᵁ V.ι ⁻¹ᵁ V ≤ V.ι ''ᵁ ⊤ := Scheme.Hom.image_mono V.ι le_top

  have nat := e.hom.mapPresheaf.naturality i₁.op
  have hx := ConcreteCategory.congr_hom nat (σ.app (V.ι ''ᵁ ⊤) (toUnitSection _ 1))
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hx
  have e1 : (Scheme.Hom.opensFunctor V.ι).map i₁ = homOfLE hj := Subsingleton.elim _ _
  rw [restrict_map, e1] at hx

  simp only [ψ, eApp]
  have e2 : rM M (hat_le V le_rfl) (σ.app V (toUnitSection V 1))
      = rM M hj (σ.app (V.ι ''ᵁ ⊤) (toUnitSection _ 1)) := by
    rw [rM_section_one, rM_section_one]
  rw [e2]
  dsimp only [rM, rO]

  have step1 : (X.presheaf.map (homOfLE (le_hat V (le_refl V))).op)
        ((e.hom.app (V.ι ⁻¹ᵁ V)).hom (M.presheaf.map (homOfLE hj).op (σ.app (V.ι ''ᵁ ⊤) (toUnitSection _ 1))))
      = (X.presheaf.map (homOfLE (le_hat V (le_refl V))).op)
        (((presheaf (SheafOfModules.unit V.toScheme.ringCatSheaf)).map i₁.op)
          (e.hom.app ⊤ (σ.app (V.ι ''ᵁ ⊤) (toUnitSection _ 1)))) :=
    congrArg (fun z => (X.presheaf.map (homOfLE (le_hat V (le_refl V))).op) z) hx
  have step2 : (X.presheaf.map (homOfLE (le_hat V (le_refl V))).op)
        (((presheaf (SheafOfModules.unit V.toScheme.ringCatSheaf)).map i₁.op)
          (e.hom.app ⊤ (σ.app (V.ι ''ᵁ ⊤) (toUnitSection _ 1))))
      = (X.presheaf.map (homOfLE (le_hat V (le_refl V)) ≫ (Scheme.Hom.opensFunctor V.ι).map i₁).op)
          (e.hom.app ⊤ (σ.app (V.ι ''ᵁ ⊤) (toUnitSection _ 1))) := by
    rw [op_comp, X.presheaf.map_comp]
    rfl
  have step3 : coeff σ V e.hom = (X.presheaf.map (eqToHom V.ι_image_top.symm).op)
      (e.hom.app ⊤ (σ.app (V.ι ''ᵁ ⊤) (toUnitSection _ 1))) := by
    show V.topIso.hom _ = _
    rw [Scheme.Opens.topIso_hom]
    rfl
  refine step1.trans (step2.trans (Eq.trans ?_ step3.symm))
  exact congrFun (congrArg (fun f => (ConcreteCategory.hom (X.presheaf.map (Quiver.Hom.op (X := V) f)) :
    Γ(X, V.ι ''ᵁ ⊤) → Γ(X, V))) (Subsingleton.elim _ _)) _

end Coeff

end AlgebraicGeometry.Scheme.Modules.RatSec

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Hom Scheme.germToFunctionField_injective Scheme.Opens.ι_appIso Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact Spec IsIntegral Scheme.Modules.mapPresheaf_app Scheme Scheme.Hom.appIso Scheme.Opens.topIso_hom Scheme.Hom.preimage_mono IsSeparated IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.toUnitSection Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible.exists_restrict_iso Scheme.IdealSheafData.IsInvertible Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul germToFunctionField ringCatSheaf Hom.id_app Hom germToFunctionField_injective Γ Opens.ι_appIso topIso_hom Modules.Hom Hom.image_preimage_eq_opensRange_inf topIso Modules.mapPresheaf_app Hom.appIso functionField Opens.topIso_hom Hom.preimage_mono affineBasicOpen affineOpens Hom.comp_app isBasis_affineOpens Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict IdealSheafData Modules.IsInvertible Modules.toUnitSection Modules.zeroSchemeIdeal Modules.IsInvertible.exists_restrict_iso IdealSheafData.IsInvertible Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq" namespace IdealSheafData p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "map map_id ideal map_comp map_ideal module moduleι invModule invModuleSection IsInvertible range_moduleIota_app_and_injective IsInvertible.isInvertible_invModule" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible" "isInvertible_invModule zeroSchemeIdeal_invModuleSection" end AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible" in
p2m_open "AlgebraicGeometry.Scheme.Modules~restrict_smul_eq" in open _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_invModule_eq_lSpaceOn.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.RatSec AlgebraicGeometry.Scheme.IdealSheafData.PresMod AlgebraicCurve _root_.CategoryTheory.MonoidalCategory in

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_divisor_range_invModule_eq_lSpaceOn'
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    {I : X.IdealSheafData} (hI : I.IsInvertible) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (D : AlgebraicCurve.Divisor K X.functionField)
      (φ : ∀ U : X.Opens, Γ(I.invModule, U) →+ (X.functionField : Type u)),
      ((∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(I.invModule, U), φ V (I.invModule.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(I.invModule, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField)) ∧
      (∀ (U : X.Opens) (s : Γ(I.invModule, U)) (y : X), y ∈ U → IsClosed ({y} : Set X) →
          (∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(I.invModule, W), ∃ a : Γ(X, W), m = a • I.invModule.presheaf.map (homOfLE h).op s) →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring →
            WithZero.exp (D v) = v.adicValuation (φ U s))) ∧
      φ ⊤ (I.invModuleSection.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) ≠ 0 ∧
      (∀ (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (y : X) (hyU : y ∈ U), IsClosed ({y} : Set X) →
          I.ideal ⟨U, hU⟩ = Ideal.span {g} →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring →
            haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
            D v + v.ord (φ ⊤ (I.invModuleSection.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))) =
              v.ord (algebraMap Γ(X, U) X.functionField g)) := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  have hM : Scheme.Modules.IsInvertible I.invModule := hI.isInvertible_invModule
  obtain ⟨D, φ, h1, h2, h3, h4, h5⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x I.invModule hM
  set σ : 𝟙_ X.Modules ⟶ I.invModule := I.invModuleSection with hσ
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have hZ : Scheme.Modules.zeroSchemeIdeal σ = I := hI.zeroSchemeIdeal_invModuleSection

  have hideal : ∀ (W : X.affineOpens) (τ : I.invModule.restrict W.1.ι ≅ 𝟙_ (W.1 : Scheme.{u}).Modules),
      I.ideal W = Ideal.span {ψ I.invModule W.1 τ le_rfl (σ.app W.1 (toUnitSection W.1 1))} := by
    intro W τ
    rw [ψ_section_eq_coeff I.invModule W.1 τ σ]
    conv_lhs => rw [← hZ]
    exact ((Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hM σ).2 W τ).1

  have key : ∀ (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (y : X) (hyU : y ∈ U), IsClosed ({y} : Set X) →
      I.ideal ⟨U, hU⟩ = Ideal.span {g} →
      ∀ v : AlgebraicCurve.Place K X.functionField,
        (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring →
        haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
        WithZero.exp (D v) * v.adicValuation (alg U g) =
          v.adicValuation (φ ⊤ (σ.app ⊤ (toUnitSection ⊤ 1))) := by
    intro U hU g y hyU hy hg v hv
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩

    obtain ⟨W, hyW, hWU, ⟨τ⟩⟩ := Scheme.Modules.IsInvertible.exists_restrict_iso hM (V := U) hyU
    haveI : Nonempty W.1 := ⟨⟨y, hyW⟩⟩

    let s : Γ(I.invModule, W.1) := frame I.invModule W.1 τ
    have hs : IsGeneratorAt I.invModule W.1 s y := isGeneratorAt_frame I.invModule W.1 τ y
    let a : Γ(X, W.1) := ψ I.invModule W.1 τ le_rfl (σ.app W.1 (toUnitSection W.1 1))
    have hσW : σ.app W.1 (toUnitSection W.1 1) = a • s := by
      have e1 := eq_smul_frame I.invModule W.1 τ le_rfl (σ.app W.1 (toUnitSection W.1 1))
      rw [rM_self] at e1
      exact e1

    have hIW1 : I.ideal W = Ideal.span {a} := hideal W τ
    have hIW2 : I.ideal W = Ideal.span {rO hWU g} := by
      rw [← I.map_ideal (U := W) (V := ⟨U, hU⟩) hWU, hg, Ideal.map_span, Set.image_singleton]
      rfl
    have hval : v.adicValuation (alg W.1 a) = v.adicValuation (alg U g) := by
      rw [adicValuation_alg_eq_of_span_eq x W.1 y hyW hy v hv a (rO hWU g) (hIW1.symm.trans hIW2), alg_rO]

    have k5 := h5 W.1 s y hyW hy (fun W' h hyW' m => hs W' h hyW' m) v hv
    have k1 : φ ⊤ (σ.app ⊤ (toUnitSection ⊤ 1)) = φ W.1 (σ.app W.1 (toUnitSection W.1 1)) := by
      rw [← rM_section_one I.invModule σ (le_top : W.1 ≤ ⊤)]
      exact (h1 ⊤ W.1 le_top inferInstance _).symm
    rw [k1, hσW, h2, Valuation.map_mul, ← k5, ← hval]
    change _ = v.adicValuation (alg W.1 a) * _
    rw [mul_comm]

  have hσ1 : σ.app ⊤ (toUnitSection ⊤ 1) ≠ 0 := by
    intro h0
    obtain ⟨U, f, hηf, g, hg, hIg⟩ := hI (genericPoint X)
    obtain ⟨W, hηW, hWU, ⟨τ⟩⟩ :=
      Scheme.Modules.IsInvertible.exists_restrict_iso hM (V := X.affineBasicOpen f) hηf
    haveI : Nonempty W.1 := ⟨⟨genericPoint X, hηW⟩⟩
    haveI : Nonempty (X.affineBasicOpen f : X.Opens) := ⟨⟨genericPoint X, hηf⟩⟩
    have hW0 : σ.app W.1 (toUnitSection W.1 1) = 0 := by
      rw [← rM_section_one I.invModule σ (le_top : W.1 ≤ ⊤), h0, rM_zero]
    have hIW1 := hideal W τ
    rw [hW0, ψ_zero] at hIW1
    have hIW2 : I.ideal W = Ideal.span {rO hWU g} := by
      rw [← I.map_ideal (U := W) (V := X.affineBasicOpen f) hWU, hIg, Ideal.map_span, Set.image_singleton]
      rfl
    have hg0 : rO hWU g = 0 := by
      have hmem : rO hWU g ∈ I.ideal W := hIW2 ▸ Ideal.mem_span_singleton_self _
      rw [hIW1] at hmem
      simpa using hmem
    have hg0' : g = 0 := rO_injective hWU (by rw [hg0, rO_zero])
    exact nonZeroDivisors.ne_zero hg hg0'
  have hf : φ ⊤ (σ.app ⊤ (toUnitSection ⊤ 1)) ≠ 0 := by
    intro h0
    exact hσ1 (h3 ⊤ inferInstance (by rw [h0, map_zero]))
  refine ⟨D, φ, ⟨h1, h2, h3, h4, h5⟩, hf, ?_⟩
  intro U hU g y hyU hy hg v hv
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  have k := key U hU g y hyU hy hg v hv
  have hf' : v.adicValuation (φ ⊤ (σ.app ⊤ (toUnitSection ⊤ 1))) ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  have hg' : v.adicValuation (alg U g) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at k
    exact hf' k.symm
  have hlog := congrArg WithZero.log k
  rw [WithZero.log_mul WithZero.exp_ne_zero hg', WithZero.log_exp] at hlog
  simp only [Place.ord]
  change D v + -WithZero.log (v.adicValuation (φ ⊤ (σ.app ⊤ (toUnitSection ⊤ 1)))) = -WithZero.log (v.adicValuation (alg U g))
  omega

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_invModule_eq_lSpaceOn.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory in
theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    {I : X.IdealSheafData} (hI : I.IsInvertible) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (D : AlgebraicCurve.Divisor K X.functionField)
      (φ : ∀ U : X.Opens, Γ(I.invModule, U) →+ (X.functionField : Type u)),
      ((∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(I.invModule, U), φ V (I.invModule.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(I.invModule, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField)) ∧
      (∀ (U : X.Opens) (s : Γ(I.invModule, U)) (y : X), y ∈ U → IsClosed ({y} : Set X) →
          (∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(I.invModule, W), ∃ a : Γ(X, W), m = a • I.invModule.presheaf.map (homOfLE h).op s) →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring →
            WithZero.exp (D v) = v.adicValuation (φ U s))) ∧
      φ ⊤ (I.invModuleSection.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) ≠ 0 ∧
      (∀ (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (y : X) (hyU : y ∈ U), IsClosed ({y} : Set X) →
          I.ideal ⟨U, hU⟩ = Ideal.span {g} →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring →
            haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
            D v + v.ord (φ ⊤ (I.invModuleSection.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))) =
              v.ord (algebraMap Γ(X, U) X.functionField g)) :=
  AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_divisor_range_invModule_eq_lSpaceOn' x hI

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_invModule_eq_lSpaceOn
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_invModule_eq_lSpaceOn (solution)
