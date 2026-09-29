-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_divisor_range_module_eq_lSpaceOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/89cb85be-b744-5205-a6ec-3946b5efb399

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
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import Theorems.Thm_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

universe u

set_option maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Hom Scheme.germToFunctionField_injective Scheme.Opens.ι_appIso Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact Spec IsIntegral Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.restrictFunctorIsoPullback Scheme.Hom.appIso Scheme.Hom.preimage_mono IsSeparated IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.ofUnitSection Scheme.IdealSheafData.IsInvertible Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Scheme.Modules.exists_forall_eq_mul_of_presentations"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul germToFunctionField ringCatSheaf Hom.id_app Hom germToFunctionField_injective Γ Opens.ι_appIso Modules.Hom Hom.image_preimage_eq_opensRange_inf Modules.mapPresheaf_app Modules.restrictFunctorIsoPullback Hom.appIso functionField Hom.preimage_mono affineOpens Hom.comp_app isBasis_affineOpens Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict IdealSheafData Modules.IsInvertible Modules.ofUnitSection IdealSheafData.IsInvertible Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Modules.exists_forall_eq_mul_of_presentations"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app restrictFunctorIsoPullback restrict_map isSheaf restrict map_smul IsInvertible toUnitSection ofUnitSection ofUnitSection_injective IsInvertible.exists_divisor_range_eq_lSpaceOn exists_forall_eq_mul_of_presentations"
namespace RatSec
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

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
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Hom Scheme.germToFunctionField_injective Scheme.Opens.ι_appIso Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact Spec IsIntegral Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.restrictFunctorIsoPullback Scheme.Hom.appIso Scheme.Hom.preimage_mono IsSeparated IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.ofUnitSection Scheme.IdealSheafData.IsInvertible Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Scheme.Modules.exists_forall_eq_mul_of_presentations"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul germToFunctionField ringCatSheaf Hom.id_app Hom germToFunctionField_injective Γ Opens.ι_appIso Modules.Hom Hom.image_preimage_eq_opensRange_inf Modules.mapPresheaf_app Modules.restrictFunctorIsoPullback Hom.appIso functionField Hom.preimage_mono affineOpens Hom.comp_app isBasis_affineOpens Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict IdealSheafData Modules.IsInvertible Modules.ofUnitSection IdealSheafData.IsInvertible Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Modules.exists_forall_eq_mul_of_presentations"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "map map_id ideal map_comp map_ideal module moduleι IsInvertible range_moduleIota_app_and_injective IsInvertible.isInvertible_module"
namespace PresMod
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn.AlgebraicGeometry.Scheme.Modules.RatSec AlgebraicCurve WithZero"

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

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Hom Scheme.germToFunctionField_injective Scheme.Opens.ι_appIso Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact Spec IsIntegral Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.restrictFunctorIsoPullback Scheme.Hom.appIso Scheme.Hom.preimage_mono IsSeparated IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.ofUnitSection Scheme.IdealSheafData.IsInvertible Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Scheme.Modules.exists_forall_eq_mul_of_presentations" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul germToFunctionField ringCatSheaf Hom.id_app Hom germToFunctionField_injective Γ Opens.ι_appIso Modules.Hom Hom.image_preimage_eq_opensRange_inf Modules.mapPresheaf_app Modules.restrictFunctorIsoPullback Hom.appIso functionField Hom.preimage_mono affineOpens Hom.comp_app isBasis_affineOpens Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict IdealSheafData Modules.IsInvertible Modules.ofUnitSection IdealSheafData.IsInvertible Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn Modules.exists_forall_eq_mul_of_presentations" namespace IdealSheafData p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "map map_id ideal map_comp map_ideal module moduleι IsInvertible range_moduleIota_app_and_injective IsInvertible.isInvertible_module" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible" "isInvertible_module" end AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible" in
open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.RatSec AlgebraicGeometry.Scheme.IdealSheafData.PresMod AlgebraicCurve in

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_divisor_range_module_eq_lSpaceOn'
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    {I : X.IdealSheafData} (hI : I.IsInvertible) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (D : AlgebraicCurve.Divisor K X.functionField)
      (φ : ∀ U : X.Opens, Γ(I.module, U) →+ (X.functionField : Type u)),
      ((∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(I.module, U), φ V (I.module.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(I.module, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField)) ∧
      (∀ (U : X.Opens) (s : Γ(I.module, U)) (y : X), y ∈ U → IsClosed ({y} : Set X) →
          (∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(I.module, W), ∃ a : Γ(X, W), m = a • I.module.presheaf.map (homOfLE h).op s) →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring →
            WithZero.exp (D v) = v.adicValuation (φ U s))) ∧
      ∃ c : X.functionField, c ≠ 0 ∧
        (∀ (U : X.Opens) [Nonempty U] (m : Γ(I.module, U)),
            φ U m = c * algebraMap Γ(X, U) X.functionField (Scheme.Modules.ofUnitSection U (I.moduleι.app U m))) ∧
        (∀ (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (y : X) (hyU : y ∈ U), IsClosed ({y} : Set X) →
            I.ideal ⟨U, hU⟩ = Ideal.span {g} →
            ∀ v : AlgebraicCurve.Place K X.functionField,
              (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring →
              haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
              D v + v.ord c + v.ord (algebraMap Γ(X, U) X.functionField g) = 0) := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  have hM : Scheme.Modules.IsInvertible I.module := hI.isInvertible_module
  obtain ⟨D, φ, h1, h2, h3, h4, h5⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x I.module hM

  have htriv : ∀ z : X, ∃ (V : X.Opens) (_ : I.module.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf),
      z ∈ V := by
    intro z
    obtain ⟨V, hzV, ⟨e⟩⟩ := hM.1 z
    exact ⟨V, (Scheme.Modules.restrictFunctorIsoPullback V.ι).app I.module ≪≫ e, hzV⟩

  let φ₀ : ∀ U : X.Opens, Γ(I.module, U) →+ (X.functionField : Type u) := fun U =>
    if hU : Nonempty U then
      { toFun := fun m => alg U (fn I U m)
        map_zero' := by rw [fn_zero, alg_zero]
        map_add' := fun m m' => by rw [fn_add, alg_add] }
    else 0
  have hφ₀ : ∀ (U : X.Opens) [hU : Nonempty U] (m : Γ(I.module, U)), φ₀ U m = alg U (fn I U m) := by
    intro U hU m
    simp only [φ₀, dif_pos hU]
    rfl
  have n1 : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(I.module, U), φ₀ V (I.module.presheaf.map (homOfLE h).op m) = φ₀ U m := by
    intro U V h hV m
    haveI := hV
    haveI : Nonempty U := let ⟨⟨z, hz⟩⟩ := hV; ⟨⟨z, h hz⟩⟩
    rw [hφ₀, hφ₀]
    change alg V (fn I V (rM I.module h m)) = _
    rw [fn_rM, alg_rO]
  have n2 : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(I.module, U)),
      φ₀ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ₀ U m := by
    intro U hU a m
    rw [hφ₀, hφ₀, fn_smul, alg_mul]
    rfl
  have n3 : ∀ U : X.Opens, Nonempty U → Function.Injective (φ₀ U) := by
    intro U hU m m' h
    rw [hφ₀, hφ₀] at h
    exact fn_injective I U (alg_injective U h)

  obtain ⟨V₀, e₀, hηV₀⟩ := htriv (genericPoint X)
  haveI : Nonempty V₀ := ⟨⟨genericPoint X, hηV₀⟩⟩
  have hsec : ∃ (U : X.Opens) (m : Γ(I.module, U)), m ≠ 0 := ⟨V₀, frame I.module V₀ e₀, frame_ne_zero I V₀ e₀⟩

  obtain ⟨c, hc0, hc⟩ := Scheme.Modules.exists_forall_eq_mul_of_presentations I.module φ₀ φ n1 h1 n2 h2 n3 h3 hsec
  refine ⟨D, φ, ⟨h1, h2, h3, h4, h5⟩, c, hc0, ?_, ?_⟩
  · intro U hU m
    rw [hc U m, hφ₀]
    rfl
  · intro U hU g y hyU hy hg v hv
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩

    obtain ⟨V, e, hyV⟩ := htriv y
    obtain ⟨W, hWaff, hyW, hWle⟩ :=
      (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show y ∈ U ⊓ V from ⟨hyU, hyV⟩)
    have hWU : W ≤ U := hWle.trans inf_le_left
    have hWV : W ≤ V := hWle.trans inf_le_right
    haveI : Nonempty W := ⟨⟨y, hyW⟩⟩

    let s : Γ(I.module, W) := rM I.module hWV (frame I.module V e)
    have hs : IsGeneratorAt I.module W s y := isGeneratorAt_rM I.module hWV _ y (isGeneratorAt_frame I.module V e y)
    let g' : Γ(X, W) := fn I W s

    have hIW : I.ideal ⟨W, hWaff⟩ = Ideal.span {rO hWU g} := by
      rw [← I.map_ideal (U := ⟨W, hWaff⟩) (V := ⟨U, hU⟩) hWU, hg, Ideal.map_span, Set.image_singleton]
      rfl
    have hspan : Ideal.span {g'} = Ideal.span {rO hWU g} := by
      rw [← hIW]
      apply le_antisymm
      · rw [Ideal.span_singleton_le_iff_mem]
        have : g' ∈ Set.range (fn I W) := ⟨s, rfl⟩
        rw [range_fn_affine I W hWaff] at this
        exact this
      · intro f hf
        have hf' : f ∈ Set.range (fn I W) := by rw [range_fn_affine I W hWaff]; exact hf
        obtain ⟨m, rfl⟩ := hf'
        obtain ⟨a, ha⟩ := hs W le_rfl hyW m
        rw [ha, rM_self, fn_smul]
        exact Ideal.mul_mem_left _ a (Ideal.mem_span_singleton_self _)

    have key := h5 W s y hyW hy (fun W' h hyW' m => hs W' h hyW' m) v hv
    rw [hc W s, hφ₀, Valuation.map_mul] at key
    change WithZero.exp (D v) = v.adicValuation c * v.adicValuation (alg W g') at key
    rw [adicValuation_alg_eq_of_span_eq x W y hyW hy v hv g' (rO hWU g) hspan, alg_rO] at key

    have hc' : v.adicValuation c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
    have hg' : v.adicValuation (alg U g) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at key
      exact WithZero.exp_ne_zero key
    have := congrArg WithZero.log key
    rw [WithZero.log_exp, WithZero.log_mul hc' hg'] at this
    simp only [Place.ord]
    change D v + -WithZero.log (v.adicValuation c) + -WithZero.log (v.adicValuation (alg U g)) = 0
    omega

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory in
theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    {I : X.IdealSheafData} (hI : I.IsInvertible) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (D : AlgebraicCurve.Divisor K X.functionField)
      (φ : ∀ U : X.Opens, Γ(I.module, U) →+ (X.functionField : Type u)),
      ((∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(I.module, U), φ V (I.module.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(I.module, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField)) ∧
      (∀ (U : X.Opens) (s : Γ(I.module, U)) (y : X), y ∈ U → IsClosed ({y} : Set X) →
          (∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(I.module, W), ∃ a : Γ(X, W), m = a • I.module.presheaf.map (homOfLE h).op s) →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring →
            WithZero.exp (D v) = v.adicValuation (φ U s))) ∧
      ∃ c : X.functionField, c ≠ 0 ∧
        (∀ (U : X.Opens) [Nonempty U] (m : Γ(I.module, U)),
            φ U m = c * algebraMap Γ(X, U) X.functionField (Scheme.Modules.ofUnitSection U (I.moduleι.app U m))) ∧
        (∀ (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (y : X) (hyU : y ∈ U), IsClosed ({y} : Set X) →
            I.ideal ⟨U, hU⟩ = Ideal.span {g} →
            ∀ v : AlgebraicCurve.Place K X.functionField,
              (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring →
              haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
              D v + v.ord c + v.ord (algebraMap Γ(X, U) X.functionField g) = 0) :=
  AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_divisor_range_module_eq_lSpaceOn' x hI

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn (solution)
