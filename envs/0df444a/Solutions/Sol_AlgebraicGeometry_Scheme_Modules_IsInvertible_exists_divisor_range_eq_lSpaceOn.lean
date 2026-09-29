-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9f91fd84-a90e-5584-8beb-c3ba67493b65

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import Theorems.Thm_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Hom Scheme.germToFunctionField_injective Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact Spec IsIntegral Scheme Scheme.Modules.restrictFunctorIsoPullback Scheme.Hom.appIso Scheme.Hom.preimage_mono IsSeparated IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "germToFunctionField ringCatSheaf Hom.id_app Hom germToFunctionField_injective Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctorIsoPullback Hom.appIso functionField Hom.preimage_mono Hom.comp_app basicOpen isBasis_affineOpens Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict Modules.IsInvertible"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app restrictFunctorIsoPullback restrict_map isSheaf restrict map_smul IsInvertible"
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

section Phi

variable [IsIntegral X] (V₀ : X.Opens) [Nonempty V₀]
  (e₀ : M.restrict V₀.ι ≅ SheafOfModules.unit V₀.toScheme.ringCatSheaf)

noncomputable def φ (W : X.Opens) [Nonempty W] (m : Γ(M, W)) : X.functionField :=
  haveI := nonempty_inf W V₀
  alg (W ⊓ V₀) (ψ M V₀ e₀ inf_le_right (rM M inf_le_left m))

theorem φ_def (W : X.Opens) [Nonempty W] (m : Γ(M, W)) :
    φ M V₀ e₀ W m = (haveI := nonempty_inf W V₀; alg (W ⊓ V₀) (ψ M V₀ e₀ inf_le_right (rM M inf_le_left m))) := rfl

theorem φ_add (W : X.Opens) [Nonempty W] (m m' : Γ(M, W)) :
    φ M V₀ e₀ W (m + m') = φ M V₀ e₀ W m + φ M V₀ e₀ W m' := by
  simp only [φ_def]
  rw [rM_add, ψ_add, alg_add]

theorem φ_zero (W : X.Opens) [Nonempty W] : φ M V₀ e₀ W 0 = 0 := by
  simp only [φ_def]
  rw [rM_zero, ψ_zero, alg_zero]

theorem φ_sub (W : X.Opens) [Nonempty W] (m m' : Γ(M, W)) :
    φ M V₀ e₀ W (m - m') = φ M V₀ e₀ W m - φ M V₀ e₀ W m' := by
  rw [eq_sub_iff_add_eq, ← φ_add, sub_add_cancel]

theorem φ_smul (W : X.Opens) [Nonempty W] (a : Γ(X, W)) (m : Γ(M, W)) :
    φ M V₀ e₀ W (a • m) = alg W a * φ M V₀ e₀ W m := by
  haveI := nonempty_inf W V₀
  simp only [φ_def]
  rw [rM_smul, ψ_smul, alg_mul, alg_rO]

theorem φ_rM {W W' : X.Opens} [Nonempty W] [Nonempty W'] (h : W' ≤ W) (m : Γ(M, W)) :
    φ M V₀ e₀ W' (rM M h m) = φ M V₀ e₀ W m := by
  haveI := nonempty_inf W V₀
  haveI := nonempty_inf W' V₀
  simp only [φ_def]
  have h' : W' ⊓ V₀ ≤ W ⊓ V₀ := inf_le_inf_right V₀ h
  have e1 : rM M (inf_le_left : W' ⊓ V₀ ≤ W') (rM M h m) = rM M h' (rM M (inf_le_left : W ⊓ V₀ ≤ W) m) := by
    rw [rM_rM, rM_rM]
  rw [e1]
  have e2 := ψ_res M V₀ e₀ (inf_le_right : W ⊓ V₀ ≤ V₀) h' (rM M (inf_le_left : W ⊓ V₀ ≤ W) m)
  rw [show ψ M V₀ e₀ (inf_le_right : W' ⊓ V₀ ≤ V₀) (rM M h' (rM M (inf_le_left : W ⊓ V₀ ≤ W) m))
      = ψ M V₀ e₀ (h'.trans inf_le_right) (rM M h' (rM M (inf_le_left : W ⊓ V₀ ≤ W) m)) from rfl, e2, alg_rO]

theorem φ_frame_self : φ M V₀ e₀ V₀ (frame M V₀ e₀) = 1 := by
  haveI := nonempty_inf V₀ V₀
  simp only [φ_def]
  rw [show ψ M V₀ e₀ (inf_le_right : V₀ ⊓ V₀ ≤ V₀) (rM M (inf_le_left : V₀ ⊓ V₀ ≤ V₀) (frame M V₀ e₀))
      = ψ M V₀ e₀ (inf_le_left : V₀ ⊓ V₀ ≤ V₀) (rM M (inf_le_left : V₀ ⊓ V₀ ≤ V₀) (frame M V₀ e₀)) from rfl,
    ψ_rM_frame, alg_one]

theorem φ_injective
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf), x ∈ V)
    (W : X.Opens) [Nonempty W] : Function.Injective (φ M V₀ e₀ W) := by
  intro m m' hmm
  rw [← sub_eq_zero] at hmm ⊢
  rw [← φ_sub] at hmm
  set n := m - m' with hn
  clear_value n
  clear hn m m'
  haveI := nonempty_inf W V₀

  have ha : rM M (inf_le_left : W ⊓ V₀ ≤ W) n = 0 := by
    apply ψ_injective M V₀ e₀ inf_le_right
    rw [ψ_zero]
    exact alg_injective (W ⊓ V₀) (by rw [alg_zero]; exact hmm)

  choose Vx ex hxV using htriv
  have hb : ∀ x : W, rM M (inf_le_left : W ⊓ Vx x ≤ W) n = 0 := by
    intro x
    haveI : Nonempty (W ⊓ Vx x : X.Opens) := ⟨⟨x, x.2, hxV x⟩⟩
    haveI := nonempty_inf (W ⊓ Vx x) V₀
    apply ψ_injective M (Vx x) (ex x) inf_le_right
    rw [ψ_zero]
    apply rO_injective (inf_le_left : (W ⊓ Vx x) ⊓ V₀ ≤ W ⊓ Vx x)
    rw [rO_zero, ← ψ_res, rM_rM]
    have e1 : rM M ((inf_le_left : (W ⊓ Vx x) ⊓ V₀ ≤ W ⊓ Vx x).trans (inf_le_left : W ⊓ Vx x ≤ W)) n
        = rM M (inf_le_inf_right V₀ inf_le_left : (W ⊓ Vx x) ⊓ V₀ ≤ W ⊓ V₀) (rM M (inf_le_left : W ⊓ V₀ ≤ W) n) := by
      rw [rM_rM]
    rw [e1, ha, rM_zero, ψ_zero]

  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  refine TopCat.Sheaf.eq_of_locally_eq' F (fun x : W => W ⊓ Vx x) W (fun x => homOfLE inf_le_left) ?_ n 0 ?_
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hy, hxV y⟩
  · intro x
    have := hb x
    simp only [rM] at this
    rw [map_zero]
    exact this

theorem φ_frame_ne_zero
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf), x ∈ V)
    (V : X.Opens) [Nonempty V] (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    φ M V₀ e₀ V (frame M V e) ≠ 0 := by
  intro h
  have h0 : frame M V e = 0 := φ_injective M V₀ e₀ htriv V (h.trans (φ_zero M V₀ e₀ V).symm)
  have h1 := ψ_frame M V e
  rw [h0, ψ_zero] at h1
  exact zero_ne_one h1

end Phi

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

variable (V₀ : X.Opens) [Nonempty V₀] (e₀ : M.restrict V₀.ι ≅ SheafOfModules.unit V₀.toScheme.ringCatSheaf)

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

theorem adicValuation_φ_le_of_isGeneratorAt (U U' : X.Opens) (s : Γ(M, U)) (s' : Γ(M, U')) (y : X)
    (hyU : y ∈ U) (hyU' : y ∈ U') (hy : IsClosed ({y} : Set X)) (hs' : IsGeneratorAt M U' s' y)
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    letI := (baseToFunctionField x).toAlgebra
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    haveI : Nonempty U' := ⟨⟨y, hyU'⟩⟩
    v.adicValuation (φ M V₀ e₀ U s) ≤ v.adicValuation (φ M V₀ e₀ U' s') := by
  letI := (baseToFunctionField x).toAlgebra
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  haveI : Nonempty U' := ⟨⟨y, hyU'⟩⟩
  haveI : Nonempty (U ⊓ U' : X.Opens) := ⟨⟨y, hyU, hyU'⟩⟩
  obtain ⟨a, ha⟩ := hs' (U ⊓ U') inf_le_right ⟨hyU, hyU'⟩ (rM M inf_le_left s)
  rw [← φ_rM M V₀ e₀ (inf_le_left : U ⊓ U' ≤ U) s, ha, φ_smul, φ_rM, Valuation.map_mul]
  calc v.adicValuation (alg (U ⊓ U') a) * v.adicValuation (φ M V₀ e₀ U' s')
      ≤ 1 * v.adicValuation (φ M V₀ e₀ U' s') :=
        mul_le_mul_left (adicValuation_alg_le_one x (U ⊓ U') y ⟨hyU, hyU'⟩ hy v hv a) _
    _ = v.adicValuation (φ M V₀ e₀ U' s') := one_mul _

theorem adicValuation_φ_eq_of_isGeneratorAt (U U' : X.Opens) (s : Γ(M, U)) (s' : Γ(M, U')) (y : X)
    (hyU : y ∈ U) (hyU' : y ∈ U') (hy : IsClosed ({y} : Set X))
    (hs : IsGeneratorAt M U s y) (hs' : IsGeneratorAt M U' s' y)
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    letI := (baseToFunctionField x).toAlgebra
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    haveI : Nonempty U' := ⟨⟨y, hyU'⟩⟩
    v.adicValuation (φ M V₀ e₀ U s) = v.adicValuation (φ M V₀ e₀ U' s') :=
  le_antisymm (adicValuation_φ_le_of_isGeneratorAt M x V₀ e₀ U U' s s' y hyU hyU' hy hs' v hv)
    (adicValuation_φ_le_of_isGeneratorAt M x V₀ e₀ U' U s' s y hyU' hyU hy hs v hv)

structure Triv where

  V : X.Opens

  e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf

open Classical in

noncomputable def dAt (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField) : ℤ :=
  letI := (baseToFunctionField x).toAlgebra
  if h : ∃ (y : X) (T : Triv M), y ∈ T.V ∧ IsClosed ({y} : Set X) ∧
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring then
    haveI : Nonempty h.choose_spec.choose.V := ⟨⟨h.choose, h.choose_spec.choose_spec.1⟩⟩
    WithZero.log (v.adicValuation (φ M V₀ e₀ h.choose_spec.choose.V (frame M h.choose_spec.choose.V h.choose_spec.choose.e)))
  else 0

theorem exp_dAt_eq [IsSeparated x]
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf), x ∈ V)
    (U : X.Opens) (s : Γ(M, U)) (y : X) (hyU : y ∈ U) (hy : IsClosed ({y} : Set X))
    (hs : IsGeneratorAt M U s y)
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    letI := (baseToFunctionField x).toAlgebra
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    exp (dAt M x V₀ e₀ v) = v.adicValuation (φ M V₀ e₀ U s) := by
  letI := (baseToFunctionField x).toAlgebra
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  obtain ⟨V, e, hyV⟩ := htriv y
  have h : ∃ (y : X) (T : Triv M), y ∈ T.V ∧ IsClosed ({y} : Set X) ∧
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring :=
    ⟨y, ⟨V, e⟩, hyV, hy, hv⟩
  rw [dAt, dif_pos h]
  obtain ⟨hy'T, hy', hv'⟩ := h.choose_spec.choose_spec
  have hyy : h.choose = y := eq_of_range_stalk_eq x _ _ (hv'.trans hv.symm)
  set T := h.choose_spec.choose with hT
  haveI : Nonempty T.V := ⟨⟨h.choose, hy'T⟩⟩
  rw [hyy] at hy'T
  have hne : φ M V₀ e₀ T.V (frame M T.V T.e) ≠ 0 := φ_frame_ne_zero M V₀ e₀ htriv T.V T.e
  rw [exp_log (Place.adicValuation_ne_zero _ hne)]
  exact adicValuation_φ_eq_of_isGeneratorAt M x V₀ e₀ T.V U (frame M T.V T.e) s y hy'T hyU hy
    (isGeneratorAt_frame M T.V T.e y) hs v hv

theorem dAt_eq_zero_of_mem [IsSeparated x]
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf), x ∈ V)
    (y : X) (hyV₀ : y ∈ V₀) (hy : IsClosed ({y} : Set X))
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    dAt M x V₀ e₀ v = 0 := by
  letI := (baseToFunctionField x).toAlgebra
  have h := exp_dAt_eq M x V₀ e₀ htriv V₀ (frame M V₀ e₀) y hyV₀ hy (isGeneratorAt_frame M V₀ e₀ y) v hv
  rw [φ_frame_self, Valuation.map_one, ← exp_zero] at h
  exact exp_injective h

omit [SmoothOfRelativeDimension 1 x] in

theorem dAt_eq_zero_of_not (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      ¬ ∃ y : X, IsClosed ({y} : Set X) ∧
        (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    dAt M x V₀ e₀ v = 0 := by
  letI := (baseToFunctionField x).toAlgebra
  rw [dAt, dif_neg]
  rintro ⟨y, T, -, hy, hvy⟩
  exact hv ⟨y, hy, hvy⟩

theorem finite_support_dAt [IsSeparated x] [QuasiCompact x]
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf), x ∈ V) :
    (Function.support (dAt M x V₀ e₀)).Finite := by
  letI := (baseToFunctionField x).toAlgebra
  have hV₀ : ((V₀ : Set X)).Nonempty := by
    obtain ⟨⟨z, hz⟩⟩ := (inferInstance : Nonempty V₀)
    exact ⟨z, hz⟩
  have hfin := finite_compl_of_isOpen x V₀ hV₀
  apply (hfin.biUnion (t := fun y => {v : Place K X.functionField |
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring}) ?_).subset
  · intro v hv
    rw [Function.mem_support] at hv
    by_cases h : ∃ y : X, IsClosed ({y} : Set X) ∧
        (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring
    · obtain ⟨y, hy, hvy⟩ := h
      refine Set.mem_biUnion (x := y) ?_ hvy
      intro hyV₀
      exact hv (dAt_eq_zero_of_mem M x V₀ e₀ htriv y hyV₀ hy v hvy)
    · exact (hv (dAt_eq_zero_of_not M x V₀ e₀ v h)).elim
  · intro y _
    apply Set.Subsingleton.finite
    intro v hv w hw
    apply Place.ext
    apply ValuationSubring.toSubring_injective
    exact hv.symm.trans hw

noncomputable def divisor [IsSeparated x] [QuasiCompact x]
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf), x ∈ V) :
    letI := (baseToFunctionField x).toAlgebra
    Divisor K X.functionField :=
  Finsupp.ofSupportFinite (dAt M x V₀ e₀) (finite_support_dAt M x V₀ e₀ htriv)

theorem divisor_apply [IsSeparated x] [QuasiCompact x]
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf), x ∈ V)
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField) :
    divisor M x V₀ e₀ htriv v = dAt M x V₀ e₀ v := by
  simp only [divisor, Finsupp.ofSupportFinite_coe]

end Places

section Main

open AlgebraicCurve WithZero

variable {K : Type u} [Field K] (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [SmoothOfRelativeDimension 1 x]
  [IsSeparated x] [QuasiCompact x]
  (V₀ : X.Opens) [Nonempty V₀] (e₀ : M.restrict V₀.ι ≅ SheafOfModules.unit V₀.toScheme.ringCatSheaf)
  (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf), x ∈ V)

theorem φ_mem_lSpaceOn (U : X.Opens) [Nonempty U] (m : Γ(M, U)) :
    letI := (baseToFunctionField x).toAlgebra
    φ M V₀ e₀ U m ∈ lSpaceOn (placesOf x U) (divisor M x V₀ e₀ htriv) := by
  letI := (baseToFunctionField x).toAlgebra
  intro v hv
  obtain ⟨y, hyU, hy, hvy⟩ := hv
  obtain ⟨V, e, hyV⟩ := htriv y
  haveI : Nonempty (U ⊓ V : X.Opens) := ⟨⟨y, hyU, hyV⟩⟩
  haveI : Nonempty V := ⟨⟨y, hyV⟩⟩
  rw [divisor_apply, exp_dAt_eq M x V₀ e₀ htriv V (frame M V e) y hyV hy (isGeneratorAt_frame M V e y) v hvy,
    ← φ_rM M V₀ e₀ (inf_le_left : U ⊓ V ≤ U) m,
    eq_smul_frame M V e (inf_le_right : U ⊓ V ≤ V) (rM M (inf_le_left : U ⊓ V ≤ U) m), φ_smul, φ_rM,
    Valuation.map_mul]
  calc v.adicValuation (alg (U ⊓ V) _) * v.adicValuation (φ M V₀ e₀ V (frame M V e))
      ≤ 1 * v.adicValuation (φ M V₀ e₀ V (frame M V e)) :=
        mul_le_mul_left (adicValuation_alg_le_one x (U ⊓ V) y ⟨hyU, hyV⟩ hy v hvy _) _
    _ = v.adicValuation (φ M V₀ e₀ V (frame M V e)) := one_mul _

theorem exists_φ_eq (U : X.Opens) (hU : IsAffineOpen U) [hne : Nonempty U] (f : X.functionField)
    (hf : letI := (baseToFunctionField x).toAlgebra
      f ∈ lSpaceOn (placesOf x U) (divisor M x V₀ e₀ htriv)) :
    ∃ m : Γ(M, U), φ M V₀ e₀ U m = f := by
  letI := (baseToFunctionField x).toAlgebra

  have htriv' := htriv
  choose Vt et hyt using htriv'
  have hW : ∀ y : U, ∃ g : Γ(X, U), X.basicOpen g ≤ U ⊓ Vt y ∧ (y : X) ∈ X.basicOpen g :=
    fun y => hU.exists_basicOpen_le (V := U ⊓ Vt y) ⟨(y : X), ⟨y.2, hyt y⟩⟩ y.2
  choose g hgle hyg using hW
  let W : U → X.Opens := fun y => X.basicOpen (g y)
  have hWU : ∀ y, W y ≤ U := fun y => (hgle y).trans inf_le_left
  have hWV : ∀ y, W y ≤ Vt y := fun y => (hgle y).trans inf_le_right
  have hWaff : ∀ y, IsAffineOpen (W y) := fun y => hU.basicOpen (g y)
  haveI hWne : ∀ y, Nonempty (W y) := fun y => ⟨⟨y, hyg y⟩⟩
  haveI hVne : ∀ y, Nonempty (Vt y) := fun y => ⟨⟨y, hyt y⟩⟩

  let c : U → X.functionField := fun y => φ M V₀ e₀ (Vt y) (frame M (Vt y) (et y))
  have hc : ∀ y, c y ≠ 0 := fun y => φ_frame_ne_zero M V₀ e₀ htriv (Vt y) (et y)
  have hreg : ∀ y : U, f * (c y)⁻¹ ∈ (algebraMap Γ(X, W y) X.functionField).range := by
    intro y
    rw [range_algebraMap_functionField_eq_iInf_of_isAffineOpen x (W y) (hWaff y)]
    refine Subring.mem_iInf.mpr fun v' => Subring.mem_iInf.mpr fun ⟨z, hzW, hz, hv'z⟩ => ?_
    apply (Place.mem_iff_adicValuation_le_one v').mpr
    have h1 : v'.adicValuation f ≤ exp (divisor M x V₀ e₀ htriv v') :=
      hf v' ⟨z, hWU y hzW, hz, hv'z⟩
    rw [divisor_apply, exp_dAt_eq M x V₀ e₀ htriv (Vt y) (frame M (Vt y) (et y)) z (hWV y hzW) hz
      (isGeneratorAt_frame M (Vt y) (et y) z) v' hv'z] at h1
    rw [Valuation.map_mul, map_inv₀]
    have hcv : v'.adicValuation (c y) ≠ 0 := (Valuation.ne_zero_iff _).mpr (hc y)
    rw [← div_eq_mul_inv]
    exact (div_le_one₀ (zero_lt_iff.mpr hcv)).mpr h1
  choose a ha using hreg

  let ml : ∀ y : U, Γ(M, W y) := fun y => a y • rM M (hWV y) (frame M (Vt y) (et y))
  have hml : ∀ y, φ M V₀ e₀ (W y) (ml y) = f := by
    intro y
    simp only [ml]
    rw [φ_smul, φ_rM]
    change (algebraMap Γ(X, W y) X.functionField) (a y) * c y = f
    rw [ha, mul_assoc, inv_mul_cancel₀ (hc y), mul_one]

  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.1 W ml := by
    intro i j
    haveI := nonempty_inf (W i) (W j)
    have key : rM M (inf_le_left : W i ⊓ W j ≤ W i) (ml i) = rM M (inf_le_right : W i ⊓ W j ≤ W j) (ml j) := by
      apply φ_injective M V₀ e₀ htriv (W i ⊓ W j)
      rw [φ_rM, φ_rM, hml, hml]
    simp only [rM] at key
    rw [show Opens.infLELeft (W i) (W j) = homOfLE inf_le_left from Subsingleton.elim _ _,
      show Opens.infLERight (W i) (W j) = homOfLE inf_le_right from Subsingleton.elim _ _]
    exact key
  have hcover : U ≤ iSup W := fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hyg ⟨z, hz⟩⟩
  obtain ⟨m, hm, -⟩ := TopCat.Sheaf.existsUnique_gluing' F W U (fun y => homOfLE (hWU y)) hcover ml hcompat
  refine ⟨m, ?_⟩
  obtain ⟨y₀⟩ := (inferInstance : Nonempty U)
  rw [← φ_rM M V₀ e₀ (hWU y₀) m]
  have hm0 : rM M (hWU y₀) m = ml y₀ := hm y₀
  rw [hm0, hml]

theorem range_φ_eq (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (baseToFunctionField x).toAlgebra
    Set.range (φ M V₀ e₀ U) = (lSpaceOn (placesOf x U) (divisor M x V₀ e₀ htriv) : Set X.functionField) := by
  letI := (baseToFunctionField x).toAlgebra
  ext f
  constructor
  · rintro ⟨m, rfl⟩
    exact φ_mem_lSpaceOn M x V₀ e₀ htriv U m
  · intro hf
    exact exists_φ_eq M x V₀ e₀ htriv U hU f hf

end Main

end AlgebraicGeometry.Scheme.Modules.RatSec

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Hom Scheme.germToFunctionField_injective Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact Spec IsIntegral Scheme Scheme.Modules.restrictFunctorIsoPullback Scheme.Hom.appIso Scheme.Hom.preimage_mono IsSeparated IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.image_mono Scheme.Hom.opensFunctor Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "germToFunctionField ringCatSheaf Hom.id_app Hom germToFunctionField_injective Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctorIsoPullback Hom.appIso functionField Hom.preimage_mono Hom.comp_app basicOpen isBasis_affineOpens Modules Opens Hom.image_mono Hom.opensFunctor Opens.opensRange_ι restrict Modules.IsInvertible" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app restrictFunctorIsoPullback restrict_map isSheaf restrict map_smul IsInvertible" namespace IsInvertible end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
open AlgebraicGeometry.Scheme.Modules.RatSec AlgebraicCurve in

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn'
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (D : AlgebraicCurve.Divisor K X.functionField) (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u)),
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField)) ∧
      (∀ (U : X.Opens) (s : Γ(M, U)) (y : X), y ∈ U → IsClosed ({y} : Set X) →
          (∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(M, W), ∃ a : Γ(X, W), m = a • M.presheaf.map (homOfLE h).op s) →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring →
            WithZero.exp (D v) = v.adicValuation (φ U s)) := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra

  have htriv : ∀ z : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf), z ∈ V := by
    intro z
    obtain ⟨V, hzV, ⟨e⟩⟩ := hM.1 z
    exact ⟨V, (Scheme.Modules.restrictFunctorIsoPullback V.ι).app M ≪≫ e, hzV⟩

  obtain ⟨V₀, e₀, hηV₀⟩ := htriv (genericPoint X)
  haveI : Nonempty V₀ := ⟨⟨genericPoint X, hηV₀⟩⟩
  let D := divisor M x V₀ e₀ htriv
  let φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u) := fun U =>
    if hU : Nonempty U then
      { toFun := fun m => φ M V₀ e₀ U m
        map_zero' := φ_zero M V₀ e₀ U
        map_add' := φ_add M V₀ e₀ U }
    else 0
  have hφ' : ∀ (U : X.Opens) [hU : Nonempty U] (m : Γ(M, U)), φ' U m = φ M V₀ e₀ U m := by
    intro U hU m
    simp only [φ', dif_pos hU]
    rfl
  refine ⟨D, φ', ?_, ?_, ?_, ?_, ?_⟩
  · intro U V h hV m
    haveI := hV
    haveI : Nonempty U := let ⟨⟨z, hz⟩⟩ := hV; ⟨⟨z, h hz⟩⟩
    rw [hφ', hφ']
    exact φ_rM M V₀ e₀ h m
  · intro U hU a m
    rw [hφ', hφ']
    exact φ_smul M V₀ e₀ U a m
  · intro U hU m m' h
    rw [hφ', hφ'] at h
    exact φ_injective M V₀ e₀ htriv U h
  · intro U hU hne
    haveI := hne
    have : (φ' U : Γ(M, U) → X.functionField) = φ M V₀ e₀ U := funext fun m => hφ' U m
    rw [this]
    exact range_φ_eq M x V₀ e₀ htriv U hU
  · intro U s y hyU hy hs v hv
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    rw [hφ']
    simp only [D, divisor_apply]
    exact exp_dAt_eq M x V₀ e₀ htriv U s y hyU hy hs v hv

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (D : AlgebraicCurve.Divisor K X.functionField) (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u)),
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField)) ∧
      (∀ (U : X.Opens) (s : Γ(M, U)) (y : X), y ∈ U → IsClosed ({y} : Set X) →
          (∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(M, W), ∃ a : Γ(X, W), m = a • M.presheaf.map (homOfLE h).op s) →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring →
            WithZero.exp (D v) = v.adicValuation (φ U s)) :=
  AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn' x M hM

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn (solution)
