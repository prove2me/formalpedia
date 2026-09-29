-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b888efa2-a35f-54f3-8bda-f3ad2ecd9f6d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicCurve_CurveModel_nonempty_pullback_ofPoint_module_iso_foldr_pow_ramificationIndexAlong_of_pointEquivPlace_comp_eq_restrictAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

noncomputable section

namespace K6H8
namespace Tw

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData"

variable {Y : Scheme.{u}}

def shuffle (A B C D : Y.Modules) : (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D) :=
  α_ A B (C ⊗ D) ≪≫ whiskerLeftIso A ((α_ B C D).symm ≪≫ whiskerRightIso (β_ B C) D ≪≫ α_ C B D) ≪≫
    (α_ A C (B ⊗ D)).symm

def shuffle' (A B C D : Y.Modules) : (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ D) ⊗ (B ⊗ C) :=
  whiskerLeftIso (A ⊗ B) (β_ C D) ≪≫ shuffle A B D C

abbrev pf (J K : Y.IdealSheafData) : Y.Modules := J.invModule ⊗ K.module

theorem nonempty_module_top_iso : Nonempty ((⊤ : Y.IdealSheafData).module ≅ 𝟙_ Y.Modules) := by
  obtain ⟨⟨e⟩, -⟩ := (isInvertible_top (X := Y)).nonempty_module_tensor_invModule_iso
  obtain ⟨μ⟩ := (isInvertible_top (X := Y)).nonempty_mul_module_iso_tensor (isInvertible_top (X := Y))
  have hμ : (⊤ : Y.IdealSheafData).module ⊗ (⊤ : Y.IdealSheafData).module ≅ (⊤ : Y.IdealSheafData).module :=
    μ.symm ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module (top_mul (⊤ : Y.IdealSheafData)))
  exact ⟨(ρ_ _).symm ≪≫ whiskerLeftIso _ e.symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso hμ _ ≪≫ e⟩

theorem nonempty_invModule_top_iso : Nonempty ((⊤ : Y.IdealSheafData).invModule ≅ 𝟙_ Y.Modules) := by
  obtain ⟨-, ⟨e⟩⟩ := (isInvertible_top (X := Y)).nonempty_module_tensor_invModule_iso
  obtain ⟨m⟩ := nonempty_module_top_iso (Y := Y)
  exact ⟨(ρ_ _).symm ≪≫ whiskerLeftIso _ m.symm ≪≫ e⟩

theorem nonempty_pf_top_top_iso : Nonempty (pf (⊤ : Y.IdealSheafData) ⊤ ≅ 𝟙_ Y.Modules) :=
  ((isInvertible_top (X := Y)).nonempty_module_tensor_invModule_iso).2

theorem IsInvertible.listProd {ι : Type v} (f : ι → Y.IdealSheafData) :
    ∀ (l : List ι), (∀ i ∈ l, (f i).IsInvertible) → (l.map f).prod.IsInvertible
  | [], _ => by simpa using (isInvertible_top (X := Y))
  | (i :: l), h => by
      rw [List.map_cons, List.prod_cons]
      exact (h i (by simp)).mul (IsInvertible.listProd f l (fun j hj => h j (by simp [hj])))

theorem IsInvertible.finsetProd {ι : Type v} (f : ι → Y.IdealSheafData) (s : Finset ι)
    (h : ∀ i ∈ s, (f i).IsInvertible) : (∏ i ∈ s, f i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isInvertible_top (X := Y))
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (by simp)).mul (ih (fun i hi => h i (by simp [hi])))

theorem nonempty_pf_mul_iso {J J' K K' : Y.IdealSheafData} (hJ : J.IsInvertible) (hJ' : J'.IsInvertible)
    (hK : K.IsInvertible) (hK' : K'.IsInvertible) :
    Nonempty (pf (J * J') (K * K') ≅ pf J K ⊗ pf J' K') := by
  obtain ⟨a⟩ := hJ.nonempty_mul_invModule_iso_tensor hJ'
  obtain ⟨b⟩ := hK.nonempty_mul_module_iso_tensor hK'
  exact ⟨(a ⊗ᵢ b) ≪≫ shuffle _ _ _ _⟩

def contract {A B C D : Y.Modules} (e : B ⊗ D ≅ 𝟙_ Y.Modules) : (A ⊗ B) ⊗ (C ⊗ D) ≅ A ⊗ C :=
  shuffle A B C D ≪≫ whiskerLeftIso _ e ≪≫ ρ_ _

theorem nonempty_pf_congr {J J' K K' : Y.IdealSheafData} (hJ : J.IsInvertible) (hJ' : J'.IsInvertible)
    (hK : K.IsInvertible) (hK' : K'.IsInvertible) (h : J * K' = J' * K) :
    Nonempty (pf J K ≅ pf J' K') := by
  obtain ⟨a⟩ := hJ.nonempty_mul_invModule_iso_tensor hK'
  obtain ⟨a'⟩ := hJ'.nonempty_mul_invModule_iso_tensor hK
  obtain ⟨-, ⟨eK⟩⟩ := hK.nonempty_module_tensor_invModule_iso
  obtain ⟨-, ⟨eK'⟩⟩ := hK'.nonempty_module_tensor_invModule_iso

  have c : J.invModule ⊗ K'.invModule ≅ J'.invModule ⊗ K.invModule :=
    a.symm ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule h) ≪≫ a'

  have l : (J.invModule ⊗ K'.invModule) ⊗ (K.module ⊗ K'.module) ≅ pf J K :=
    contract eK'
  have r : (J'.invModule ⊗ K.invModule) ⊗ (K.module ⊗ K'.module) ≅ pf J' K' :=
    whiskerLeftIso _ (β_ _ _) ≪≫ contract eK
  exact ⟨l.symm ≪≫ whiskerRightIso c _ ≪≫ r⟩

variable {V : Type v}

def twistL (P : V → Y.IdealSheafData) (D : V → ℤ) (l : List V) : Y.Modules :=
  l.foldr (fun v M => (P v ^ (D v).toNat).invModule ⊗ ((P v ^ (-(D v)).toNat).module ⊗ M)) (𝟙_ Y.Modules)

@[scoped simp] theorem twistL_nil (P : V → Y.IdealSheafData) (D : V → ℤ) : twistL P D [] = 𝟙_ Y.Modules := rfl

@[scoped simp] theorem twistL_cons (P : V → Y.IdealSheafData) (D : V → ℤ) (v : V) (l : List V) :
    twistL P D (v :: l) = (P v ^ (D v).toNat).invModule ⊗ ((P v ^ (-(D v)).toNat).module ⊗ twistL P D l) := rfl

theorem nonempty_twistL_iso_of_forall_eq (P P' : V → Y.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V), (∀ v ∈ l, P v = P' v) → Nonempty (twistL P D l ≅ twistL P' D l)
  | [], _ => ⟨(Iso.refl (𝟙_ Y.Modules) : twistL P D [] ≅ twistL P' D [])⟩
  | (v :: l), h => by
      obtain ⟨e⟩ := nonempty_twistL_iso_of_forall_eq P P' D l (fun w hw => h w (by simp [hw]))
      have hv : P v = P' v := h v (by simp)
      refine ⟨?_⟩
      change (P v ^ (D v).toNat).invModule ⊗ ((P v ^ (-(D v)).toNat).module ⊗ twistL P D l) ≅
        (P' v ^ (D v).toNat).invModule ⊗ ((P' v ^ (-(D v)).toNat).module ⊗ twistL P' D l)
      exact eqToIso (congrArg (fun I : Y.IdealSheafData => (I ^ (D v).toNat).invModule) hv) ⊗ᵢ
        (eqToIso (congrArg (fun I : Y.IdealSheafData => (I ^ (-(D v)).toNat).module) hv) ⊗ᵢ e)

abbrev Jp (P : V → Y.IdealSheafData) (D : V → ℤ) (l : List V) : Y.IdealSheafData :=
  (l.map fun v => P v ^ (D v).toNat).prod
abbrev Jn (P : V → Y.IdealSheafData) (D : V → ℤ) (l : List V) : Y.IdealSheafData :=
  (l.map fun v => P v ^ (-(D v)).toNat).prod

theorem isInvertible_Jp (P : V → Y.IdealSheafData) (D : V → ℤ) (l : List V) (h : ∀ v ∈ l, (P v).IsInvertible) :
    (Jp P D l).IsInvertible :=
  IsInvertible.listProd _ l (fun v hv => (h v hv).pow _)
theorem isInvertible_Jn (P : V → Y.IdealSheafData) (D : V → ℤ) (l : List V) (h : ∀ v ∈ l, (P v).IsInvertible) :
    (Jn P D l).IsInvertible :=
  IsInvertible.listProd _ l (fun v hv => (h v hv).pow _)

theorem nonempty_twistL_iso_pf (P : V → Y.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V), (∀ v ∈ l, (P v).IsInvertible) → Nonempty (twistL P D l ≅ pf (Jp P D l) (Jn P D l))
  | [], _ => ⟨(nonempty_pf_top_top_iso (Y := Y)).some.symm⟩
  | (v :: l), h => by
      have hv : (P v).IsInvertible := h v (by simp)
      have hl : ∀ w ∈ l, (P w).IsInvertible := fun w hw => h w (by simp [hw])
      obtain ⟨e⟩ := nonempty_twistL_iso_pf P D l hl
      obtain ⟨m⟩ := nonempty_pf_mul_iso (hv.pow (D v).toNat) (isInvertible_Jp P D l hl)
        (hv.pow (-(D v)).toNat) (isInvertible_Jn P D l hl)
      refine ⟨whiskerLeftIso _ (whiskerLeftIso _ e) ≪≫ (α_ _ _ _).symm ≪≫ m.symm ≪≫ eqToIso ?_⟩
      simp [Jp, Jn]

theorem isInvertible_twistL (P : V → Y.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V), (∀ v ∈ l, (P v).IsInvertible) → Scheme.Modules.IsInvertible (twistL P D l)
  | [], _ => Scheme.Modules.isInvertible_unit Y
  | (v :: l), h => by
      have hv : (P v).IsInvertible := h v (by simp)
      rw [twistL_cons]
      exact (hv.pow _).isInvertible_invModule.tensor
        ((hv.pow _).isInvertible_module.tensor (isInvertible_twistL P D l (fun w hw => h w (by simp [hw]))))

theorem nonempty_twistL_iso_unit_of_forall_eq_top (P : V → Y.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V), (∀ v ∈ l, P v = ⊤) → Nonempty (twistL P D l ≅ 𝟙_ Y.Modules)
  | [], _ => ⟨Iso.refl _⟩
  | (v :: l), h => by
      obtain ⟨e⟩ := nonempty_twistL_iso_unit_of_forall_eq_top P D l (fun w hw => h w (by simp [hw]))
      obtain ⟨a⟩ := nonempty_invModule_top_iso (Y := Y)
      obtain ⟨b⟩ := nonempty_module_top_iso (Y := Y)
      have hv : P v = ⊤ := h v (by simp)
      have ha : (P v ^ (D v).toNat).invModule ≅ 𝟙_ Y.Modules :=
        eqToIso (by rw [hv, ← one_eq_top, one_pow]) ≪≫ a
      have hb : (P v ^ (-(D v)).toNat).module ≅ 𝟙_ Y.Modules :=
        eqToIso (by rw [hv, ← one_eq_top, one_pow]) ≪≫ b
      exact ⟨(ha ⊗ᵢ (hb ⊗ᵢ e)) ≪≫ whiskerLeftIso _ (λ_ _) ≪≫ λ_ _⟩

theorem comap_pow {Y' : Scheme.{u}} (I : Y.IdealSheafData) (f : Y' ⟶ Y) :
    ∀ n : ℕ, (I ^ n).comap f = I.comap f ^ n
  | 0 => by rw [pow_zero, pow_zero, one_eq_top, one_eq_top, comap_top]
  | (n + 1) => by rw [pow_succ, pow_succ, comap_mul, comap_pow I f n]

theorem nonempty_pullback_twistL_iso {Y' : Scheme.{u}} (f : Y' ⟶ Y) (P : V → Y.IdealSheafData)
    (Q : V → Y'.IdealSheafData) (D : V → ℤ) :
    ∀ (l : List V), (∀ v ∈ l, (P v).IsInvertible ∧ (P v).comap f = Q v ∧ (Q v).IsInvertible) →
      Nonempty ((Scheme.Modules.pullback f).obj (twistL P D l) ≅ twistL Q D l)
  | [], _ => ⟨Scheme.Modules.pullbackTensorUnitObjIso f⟩
  | (v :: l), h => by
      obtain ⟨hP, hPQ, hQ⟩ := h v (by simp)
      obtain ⟨e⟩ := nonempty_pullback_twistL_iso f P Q D l (fun w hw => h w (by simp [hw]))
      have hc : ∀ n : ℕ, ((P v ^ n).comap f) = Q v ^ n := fun n => by rw [comap_pow, hPQ]
      have hc' : ∀ n : ℕ, ((P v ^ n).comap f).IsInvertible := fun n => by rw [hc]; exact hQ.pow n

      have em : (Scheme.Modules.pullback f).obj ((P v ^ (-(D v)).toNat).module) ≅ (Q v ^ (-(D v)).toNat).module := by
        haveI := (hP.pow (-(D v)).toNat).isIso_pullbackModuleComparison f (hc' _)
        exact asIso ((P v ^ (-(D v)).toNat).pullbackModuleComparison f) ≪≫
          eqToIso (congrArg Scheme.IdealSheafData.module (hc _))

      obtain ⟨ei0⟩ := (hP.pow (D v).toNat).nonempty_pullback_invModule_iso f (hc' _)
      have ei : (Scheme.Modules.pullback f).obj ((P v ^ (D v).toNat).invModule) ≅ (Q v ^ (D v).toNat).invModule :=
        ei0 ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule (hc _))
      refine ⟨?_⟩
      change (Scheme.Modules.pullback f).obj ((P v ^ (D v).toNat).invModule ⊗ ((P v ^ (-(D v)).toNat).module ⊗ twistL P D l)) ≅
        (Q v ^ (D v).toNat).invModule ⊗ ((Q v ^ (-(D v)).toNat).module ⊗ twistL Q D l)
      exact Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
        (ei ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ (em ⊗ᵢ e)))

open Classical in
theorem Jp_toList_eq (P : V → Y.IdealSheafData) (D : V →₀ ℤ) (s : Finset V) (hs : D.support ⊆ s) :
    Jp P D D.support.toList = ∏ v ∈ s, P v ^ (D v).toNat := by
  rw [Jp, Finset.prod_map_toList]
  refine Finset.prod_subset hs (fun v _ hv => ?_)
  rw [Finsupp.notMem_support_iff.mp hv]; simp

open Classical in
theorem Jn_toList_eq (P : V → Y.IdealSheafData) (D : V →₀ ℤ) (s : Finset V) (hs : D.support ⊆ s) :
    Jn P D D.support.toList = ∏ v ∈ s, P v ^ (-(D v)).toNat := by
  rw [Jn, Finset.prod_map_toList]
  refine Finset.prod_subset hs (fun v _ hv => ?_)
  rw [Finsupp.notMem_support_iff.mp hv]; simp

abbrev twist (P : V → Y.IdealSheafData) (D : V →₀ ℤ) : Y.Modules := twistL P D D.support.toList

open Classical in
theorem nonempty_twist_add_iso (P : V → Y.IdealSheafData) (D D' : V →₀ ℤ)
    (h : ∀ v ∈ D.support ∪ D'.support, (P v).IsInvertible) :
    Nonempty (twist P (D + D') ≅ twist P D ⊗ twist P D') := by
  set s := D.support ∪ D'.support with hs_def
  have hD : D.support ⊆ s := Finset.subset_union_left
  have hD' : D'.support ⊆ s := Finset.subset_union_right
  have hDD' : (D + D').support ⊆ s := Finsupp.support_add
  have hinv : ∀ (E : V →₀ ℤ), E.support ⊆ s → ∀ v ∈ E.support.toList, (P v).IsInvertible :=
    fun E hE v hv => h v (hE (Finset.mem_toList.mp hv))
  have hPs : ∀ (g : V → ℕ), (∏ v ∈ s, P v ^ g v).IsInvertible :=
    fun g => IsInvertible.finsetProd _ s (fun v hv => (h v hv).pow _)
  obtain ⟨e⟩ := nonempty_twistL_iso_pf P (⇑(D + D')) (D + D').support.toList (hinv _ hDD')
  obtain ⟨e₁⟩ := nonempty_twistL_iso_pf P D D.support.toList (hinv _ hD)
  obtain ⟨e₂⟩ := nonempty_twistL_iso_pf P D' D'.support.toList (hinv _ hD')
  rw [Jp_toList_eq P _ s hDD', Jn_toList_eq P _ s hDD'] at e
  rw [Jp_toList_eq P _ s hD, Jn_toList_eq P _ s hD] at e₁
  rw [Jp_toList_eq P _ s hD', Jn_toList_eq P _ s hD'] at e₂

  have key : (∏ v ∈ s, P v ^ ((D + D') v).toNat) * ((∏ v ∈ s, P v ^ (-(D v)).toNat) * ∏ v ∈ s, P v ^ (-(D' v)).toNat) =
      ((∏ v ∈ s, P v ^ (D v).toNat) * ∏ v ∈ s, P v ^ (D' v).toNat) * ∏ v ∈ s, P v ^ (-((D + D') v)).toNat := by
    simp only [← Finset.prod_mul_distrib, ← pow_add]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    congr 1
    simp only [Finsupp.coe_add, Pi.add_apply]
    omega
  obtain ⟨c⟩ := nonempty_pf_congr (hPs _) ((hPs _).mul (hPs _)) (hPs _) ((hPs _).mul (hPs _)) key
  obtain ⟨m⟩ := nonempty_pf_mul_iso (hPs fun v => (D v).toNat) (hPs fun v => (D' v).toNat)
    (hPs fun v => (-(D v)).toNat) (hPs fun v => (-(D' v)).toNat)
  exact ⟨e ≪≫ c ≪≫ m ≪≫ (e₁.symm ⊗ᵢ e₂.symm)⟩

theorem twist_zero (P : V → Y.IdealSheafData) : twist P (0 : V →₀ ℤ) = 𝟙_ Y.Modules := by
  simp [twist, twistL]

theorem isInvertible_twist (P : V → Y.IdealSheafData) (D : V →₀ ℤ) (h : ∀ v ∈ D.support, (P v).IsInvertible) :
    Scheme.Modules.IsInvertible (twist P D) :=
  isInvertible_twistL P D _ (fun v hv => h v (Finset.mem_toList.mp hv))

open Classical in
theorem nonempty_twist_single_sub_single_iso (P : V → Y.IdealSheafData) (u w : V)
    (hu : (P u).IsInvertible) (hw : (P w).IsInvertible) :
    Nonempty (twist P (Finsupp.single u 1 - Finsupp.single w 1) ≅ (P u).invModule ⊗ (P w).module) := by
  set D : V →₀ ℤ := Finsupp.single u 1 - Finsupp.single w 1 with hD
  have hsupp : D.support ⊆ {u, w} := by
    intro v hv
    have h := Finsupp.support_sub hv
    simp only [Finset.mem_union] at h
    rcases h with h | h
    · have := Finsupp.support_single_subset h; simp_all
    · have := Finsupp.support_single_subset h; simp_all
  have hinv : ∀ v ∈ D.support.toList, (P v).IsInvertible := by
    intro v hv
    have := hsupp (Finset.mem_toList.mp hv)
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl <;> assumption
  have hPs : ∀ (g : V → ℕ), (∏ v ∈ ({u, w} : Finset V), P v ^ g v).IsInvertible := by
    intro g
    refine IsInvertible.finsetProd _ _ (fun v hv => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> exact IsInvertible.pow ‹_› _
  obtain ⟨e⟩ := nonempty_twistL_iso_pf P (⇑D) D.support.toList hinv
  rw [Jp_toList_eq P D {u, w} hsupp, Jn_toList_eq P D {u, w} hsupp] at e

  have key : (∏ v ∈ ({u, w} : Finset V), P v ^ (D v).toNat) * P w = P u * ∏ v ∈ ({u, w} : Finset V), P v ^ (-(D v)).toNat := by
    by_cases huw : u = w
    · subst huw
      simp [hD]
    · rw [Finset.prod_pair huw, Finset.prod_pair huw]
      simp [hD, Finsupp.single_apply, huw, Ne.symm huw]
  obtain ⟨c⟩ := nonempty_pf_congr (hPs _) hu (hPs _) hw key
  exact ⟨e ≪≫ c⟩

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData"

theorem nonempty_pullback_pf_iso {Y' : Scheme.{u}} (f : Y' ⟶ Y) {J K : Y.IdealSheafData}
    (hJ : J.IsInvertible) (hK : K.IsInvertible) (hJ' : (J.comap f).IsInvertible) (hK' : (K.comap f).IsInvertible) :
    Nonempty ((Scheme.Modules.pullback f).obj (pf J K) ≅ pf (J.comap f) (K.comap f)) := by
  obtain ⟨ei⟩ := hJ.nonempty_pullback_invModule_iso f hJ'
  haveI := hK.isIso_pullbackModuleComparison f hK'
  exact ⟨Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ (ei ⊗ᵢ asIso (K.pullbackModuleComparison f))⟩

def twistL₂ {ι : Type v} (P : ι → Y.IdealSheafData) (pos neg : ι → ℕ) (l : List ι) : Y.Modules :=
  l.foldr (fun i M => (P i ^ pos i).invModule ⊗ ((P i ^ neg i).module ⊗ M)) (𝟙_ Y.Modules)

@[scoped simp] theorem twistL₂_nil {ι : Type v} (P : ι → Y.IdealSheafData) (pos neg : ι → ℕ) :
    twistL₂ P pos neg [] = 𝟙_ Y.Modules := rfl
@[scoped simp] theorem twistL₂_cons {ι : Type v} (P : ι → Y.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (l : List ι) :
    twistL₂ P pos neg (i :: l) = (P i ^ pos i).invModule ⊗ ((P i ^ neg i).module ⊗ twistL₂ P pos neg l) := rfl

abbrev Jp₂ {ι : Type v} (P : ι → Y.IdealSheafData) (pos : ι → ℕ) (l : List ι) : Y.IdealSheafData :=
  (l.map fun i => P i ^ pos i).prod

theorem isInvertible_Jp₂ {ι : Type v} (P : ι → Y.IdealSheafData) (pos : ι → ℕ) (l : List ι)
    (h : ∀ i ∈ l, (P i).IsInvertible) : (Jp₂ P pos l).IsInvertible :=
  IsInvertible.listProd _ l (fun i hi => (h i hi).pow _)

theorem nonempty_twistL₂_iso_pf {ι : Type v} (P : ι → Y.IdealSheafData) (pos neg : ι → ℕ) :
    ∀ (l : List ι), (∀ i ∈ l, (P i).IsInvertible) → Nonempty (twistL₂ P pos neg l ≅ pf (Jp₂ P pos l) (Jp₂ P neg l))
  | [], _ => ⟨(nonempty_pf_top_top_iso (Y := Y)).some.symm⟩
  | (i :: l), h => by
      have hi : (P i).IsInvertible := h i (by simp)
      have hl : ∀ w ∈ l, (P w).IsInvertible := fun w hw => h w (by simp [hw])
      obtain ⟨e⟩ := nonempty_twistL₂_iso_pf P pos neg l hl
      obtain ⟨m⟩ := nonempty_pf_mul_iso (hi.pow (pos i)) (isInvertible_Jp₂ P pos l hl)
        (hi.pow (neg i)) (isInvertible_Jp₂ P neg l hl)
      refine ⟨whiskerLeftIso _ (whiskerLeftIso _ e) ≪≫ (α_ _ _ _).symm ≪≫ m.symm ≪≫ eqToIso ?_⟩
      simp [Jp₂]

theorem isInvertible_twistL₂ {ι : Type v} (P : ι → Y.IdealSheafData) (pos neg : ι → ℕ) :
    ∀ (l : List ι), (∀ i ∈ l, (P i).IsInvertible) → Scheme.Modules.IsInvertible (twistL₂ P pos neg l)
  | [], _ => Scheme.Modules.isInvertible_unit Y
  | (i :: l), h => by
      have hi : (P i).IsInvertible := h i (by simp)
      rw [twistL₂_cons]
      exact (hi.pow _).isInvertible_invModule.tensor
        ((hi.pow _).isInvertible_module.tensor (isInvertible_twistL₂ P pos neg l (fun w hw => h w (by simp [hw]))))

theorem nonempty_pullback_top_module_iso {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    Nonempty ((Scheme.Modules.pullback g).obj (⊤ : Y.IdealSheafData).module ≅ (⊤ : Y'.IdealSheafData).module) := by
  obtain ⟨a⟩ := nonempty_module_top_iso (Y := Y)
  obtain ⟨b⟩ := nonempty_module_top_iso (Y := Y')
  exact ⟨(Scheme.Modules.pullback g).mapIso a ≪≫ Scheme.Modules.pullbackTensorUnitObjIso g ≪≫ b.symm⟩

theorem nonempty_pullback_pow_module_iso {Y' : Scheme.{u}} (g : Y' ⟶ Y) {K : Y.IdealSheafData} {L : Y'.IdealSheafData}
    (hK : K.IsInvertible) (hL : L.IsInvertible) (em : Nonempty ((Scheme.Modules.pullback g).obj K.module ≅ L.module)) :
    ∀ n : ℕ, Nonempty ((Scheme.Modules.pullback g).obj (K ^ n).module ≅ (L ^ n).module)
  | 0 => by
      rw [pow_zero, pow_zero, one_eq_top, one_eq_top]
      exact nonempty_pullback_top_module_iso g
  | (n + 1) => by
      obtain ⟨e⟩ := nonempty_pullback_pow_module_iso g hK hL em n
      obtain ⟨a⟩ := (hK.pow n).nonempty_mul_module_iso_tensor hK
      obtain ⟨b⟩ := (hL.pow n).nonempty_mul_module_iso_tensor hL
      rw [pow_succ, pow_succ]
      exact ⟨(Scheme.Modules.pullback g).mapIso a ≪≫ Scheme.Modules.pullbackTensorObjIso g _ _ ≪≫ (e ⊗ᵢ em.some) ≪≫ b.symm⟩

theorem nonempty_pullback_listProd_module_iso {Y' : Scheme.{u}} (g : Y' ⟶ Y) {ι : Type v}
    (K : ι → Y.IdealSheafData) (L : ι → Y'.IdealSheafData)
    (hK : ∀ i, (K i).IsInvertible) (hL : ∀ i, (L i).IsInvertible)
    (em : ∀ i, Nonempty ((Scheme.Modules.pullback g).obj (K i).module ≅ (L i).module)) (n : ι → ℕ) :
    ∀ l : List ι, Nonempty ((Scheme.Modules.pullback g).obj (l.map fun i => K i ^ n i).prod.module ≅
      (l.map fun i => L i ^ n i).prod.module)
  | [] => by simpa using nonempty_pullback_top_module_iso (Y := Y) g
  | (i :: l) => by
      obtain ⟨e⟩ := nonempty_pullback_listProd_module_iso g K L hK hL em n l
      obtain ⟨p⟩ := nonempty_pullback_pow_module_iso g (hK i) (hL i) (em i) (n i)
      obtain ⟨a⟩ := ((hK i).pow (n i)).nonempty_mul_module_iso_tensor
        (IsInvertible.listProd _ l (fun j _ => (hK j).pow _))
      obtain ⟨b⟩ := ((hL i).pow (n i)).nonempty_mul_module_iso_tensor
        (IsInvertible.listProd _ l (fun j _ => (hL j).pow _))
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
      exact ⟨(Scheme.Modules.pullback g).mapIso a ≪≫ Scheme.Modules.pullbackTensorObjIso g _ _ ≪≫ (p ⊗ᵢ e) ≪≫ b.symm⟩

theorem nonempty_pullback_invModule_iso_of_module_iso {Y' : Scheme.{u}} (g : Y' ⟶ Y) {J : Y.IdealSheafData} {J' : Y'.IdealSheafData}
    (hJ : J.IsInvertible) (em : Nonempty ((Scheme.Modules.pullback g).obj J.module ≅ J'.module)) :
    Nonempty ((Scheme.Modules.pullback g).obj J.invModule ≅ J'.invModule) := by
  obtain ⟨d⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_dual g hJ.isInvertible_module
  exact ⟨d ≪≫ Scheme.Modules.dualMapIso em.some⟩

theorem nonempty_pullback_pf_iso_of_module_iso {Y' : Scheme.{u}} (g : Y' ⟶ Y) {J K : Y.IdealSheafData} {J' K' : Y'.IdealSheafData}
    (hJ : J.IsInvertible) (eJ : Nonempty ((Scheme.Modules.pullback g).obj J.module ≅ J'.module))
    (eK : Nonempty ((Scheme.Modules.pullback g).obj K.module ≅ K'.module)) :
    Nonempty ((Scheme.Modules.pullback g).obj (pf J K) ≅ pf J' K') := by
  obtain ⟨a⟩ := nonempty_pullback_invModule_iso_of_module_iso g hJ eJ
  exact ⟨Scheme.Modules.pullbackTensorObjIso g _ _ ≪≫ (a ⊗ᵢ eK.some)⟩

theorem nonempty_foldr_pow_module_iso_listProd_module {W : Type v} (P : W → Y.IdealSheafData) (e : W → ℕ)
    (h : ∀ w, (P w).IsInvertible) :
    ∀ l : List W, Nonempty (l.foldr (fun w N => ((P w) ^ (e w)).module ⊗ N) (𝟙_ Y.Modules) ≅
      (l.map fun w => P w ^ e w).prod.module)
  | [] => ⟨(nonempty_module_top_iso (Y := Y)).some.symm ≪≫ eqToIso (by simp)⟩
  | (w :: l) => by
      obtain ⟨ih⟩ := nonempty_foldr_pow_module_iso_listProd_module P e h l
      obtain ⟨m⟩ := ((h w).pow (e w)).nonempty_mul_module_iso_tensor (IsInvertible.listProd _ l (fun j _ => (h j).pow _))
      rw [List.foldr_cons, List.map_cons, List.prod_cons]
      exact ⟨whiskerLeftIso _ ih ≪≫ m.symm⟩

theorem nonempty_pullback_twistL₂_iso {Y' : Scheme.{u}} (f : Y' ⟶ Y) {ι : Type v} (P : ι → Y.IdealSheafData)
    (Q : ι → Y'.IdealSheafData) (pos neg : ι → ℕ) :
    ∀ (l : List ι), (∀ i ∈ l, (P i).IsInvertible ∧ (P i).comap f = Q i ∧ (Q i).IsInvertible) →
      Nonempty ((Scheme.Modules.pullback f).obj (twistL₂ P pos neg l) ≅ twistL₂ Q pos neg l)
  | [], _ => ⟨Scheme.Modules.pullbackTensorUnitObjIso f⟩
  | (i :: l), h => by
      obtain ⟨hP, hPQ, hQ⟩ := h i (by simp)
      obtain ⟨e⟩ := nonempty_pullback_twistL₂_iso f P Q pos neg l (fun w hw => h w (by simp [hw]))
      have hc : ∀ n : ℕ, ((P i ^ n).comap f) = Q i ^ n := fun n => by rw [comap_pow, hPQ]
      have hc' : ∀ n : ℕ, ((P i ^ n).comap f).IsInvertible := fun n => by rw [hc]; exact hQ.pow n
      have em : (Scheme.Modules.pullback f).obj ((P i ^ neg i).module) ≅ (Q i ^ neg i).module := by
        haveI := (hP.pow (neg i)).isIso_pullbackModuleComparison f (hc' _)
        exact asIso ((P i ^ neg i).pullbackModuleComparison f) ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module (hc _))
      obtain ⟨ei0⟩ := (hP.pow (pos i)).nonempty_pullback_invModule_iso f (hc' _)
      have ei : (Scheme.Modules.pullback f).obj ((P i ^ pos i).invModule) ≅ (Q i ^ pos i).invModule :=
        ei0 ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule (hc _))
      refine ⟨?_⟩
      change (Scheme.Modules.pullback f).obj ((P i ^ pos i).invModule ⊗ ((P i ^ neg i).module ⊗ twistL₂ P pos neg l)) ≅
        (Q i ^ pos i).invModule ⊗ ((Q i ^ neg i).module ⊗ twistL₂ Q pos neg l)
      exact Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ (ei ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ (em ⊗ᵢ e)))

theorem ker_comp_comap_of_isIso {T P P' : Scheme.{u}} (a : T ⟶ P') [IsClosedImmersion a] (e : P' ⟶ P) [IsIso e] :
    (a ≫ e).ker.comap e = a.ker := by
  rw [← ker_fst_of_isClosedImmersion (a ≫ e) e]
  have h : pullback.lift a (𝟙 T) (by simp) ≫ pullback.fst e (a ≫ e) = a := pullback.lift_fst _ _ _
  haveI : IsIso (pullback.lift a (𝟙 T) (by simp : a ≫ e = 𝟙 T ≫ (a ≫ e))) := by
    have h2 : pullback.lift a (𝟙 T) (by simp : a ≫ e = 𝟙 T ≫ (a ≫ e)) ≫ pullback.snd e (a ≫ e) = 𝟙 T := pullback.lift_snd _ _ _
    haveI : IsIso (pullback.lift a (𝟙 T) (by simp : a ≫ e = 𝟙 T ≫ (a ≫ e)) ≫ pullback.snd e (a ≫ e)) := by rw [h2]; infer_instance
    exact IsIso.of_isIso_comp_right _ (pullback.snd e (a ≫ e))
  have h3 : (pullback.lift a (𝟙 T) (by simp : a ≫ e = 𝟙 T ≫ (a ≫ e)) ≫ pullback.fst e (a ≫ e)).ker = (pullback.fst e (a ≫ e)).ker :=
    Scheme.Hom.ker_comp_of_isIso _ _
  rw [← h3, h]

end K6H8.Tw
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong.K6H8 P2MW.S_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong.K6H8.Tw"
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong.K6H8"

namespace K6H8

p2m_open "AlgebraicCurve NeronModelInfra P2MW.S_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong.K6H8.Tw AlgebraicGeometry.Scheme.IdealSheafData"

abbrev placeIdeal {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [Algebra k F] (M : CurveModel k F) (W : Place k F) :
    (pullback M.toBase (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData :=
  (RelEffCartierDiv.ofPoint M.toBase (M.pointEquivPlace.symm W).1 (M.pointEquivPlace.symm W).2).I

theorem isInvertible_placeIdeal {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [Algebra k F] (M : CurveModel k F) (W : Place k F) :
    (placeIdeal M W).IsInvertible :=
  RelEffCartierDiv.isInvertible_I _

open Classical in

theorem nonempty_pullback_twistL₂_ofPoint_iso_twist
    {k : Type u} [Field k] [IsAlgClosed k]
    {F : Type v} [Field F] [Algebra k F] [HasPrincipalDivisors k F] {F' : Type v} [Field F'] [Algebra k F'] [HasPrincipalDivisors k F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (g : M'.C ⟶ M.C) (hg : g ≫ M.toBase = M'.toBase)
    (hgφ : ∀ x' : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      M.pointEquivPlace ⟨x'.1 ≫ g, by rw [Category.assoc, hg]; exact x'.2⟩ = (M'.pointEquivPlace x').restrictAlong φ hφ)
    (gk : pullback M'.toBase (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback M.toBase (𝟙 (Spec (CommRingCat.of k))))
    (hgk₁ : gk ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g) (hgk₂ : gk ≫ pullback.snd _ _ = pullback.snd _ _)
    {n : ℕ} (x : Fin n → {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (pos neg : Fin n → ℕ)
    (Dbar : Divisor k F')
    (hDbar : ∀ W : Place k F', Dbar W = (Place.ramificationIndexAlong φ W : ℤ) *
      ∑ i, (if M.pointEquivPlace (x i) = W.restrictAlong φ hφ then ((pos i : ℤ) - (neg i : ℤ)) else 0)) :
    Nonempty ((Scheme.Modules.pullback gk).obj
        (twistL₂ (fun i => (RelEffCartierDiv.ofPoint M.toBase (x i).1 (x i).2).I) pos neg (List.finRange n)) ≅
      twist (placeIdeal M') Dbar) := by

  set K : Fin n → (pullback M.toBase (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData :=
    fun i => (RelEffCartierDiv.ofPoint M.toBase (x i).1 (x i).2).I with hK
  have hKinv : ∀ i, (K i).IsInvertible := fun i => RelEffCartierDiv.isInvertible_I _
  let fib : Fin n → Finset (Place k F') := fun i => Place.fiberAlong φ hφ (M.pointEquivPlace (x i))
  let e : Place k F' → ℕ := fun W => Place.ramificationIndexAlong φ W
  let L : Fin n → (pullback M'.toBase (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData :=
    fun i => ((fib i).toList.map fun W => placeIdeal M' W ^ e W).prod
  have hLinv : ∀ i, (L i).IsInvertible := fun i =>
    IsInvertible.listProd _ _ (fun W _ => (isInvertible_placeIdeal M' W).pow _)

  have em : ∀ i, Nonempty ((Scheme.Modules.pullback gk).obj (K i).module ≅ (L i).module) := by
    intro i
    obtain ⟨c⟩ := AlgebraicCurve.CurveModel.nonempty_pullback_ofPoint_module_iso_foldr_pow_ramificationIndexAlong_of_pointEquivPlace_comp_eq_restrictAlong
      M M' φ hφ g hg hgφ gk hgk₁ hgk₂ (x i)
    obtain ⟨f⟩ := nonempty_foldr_pow_module_iso_listProd_module (placeIdeal M') e (isInvertible_placeIdeal M') (fib i).toList
    have f' : ((Place.fiberAlong φ hφ (M.pointEquivPlace (x i))).toList.foldr
        (fun W N => ((RelEffCartierDiv.ofPoint M'.toBase (M'.pointEquivPlace.symm W).1 (M'.pointEquivPlace.symm W).2).I ^
          (Place.ramificationIndexAlong φ W)).module ⊗ N)
        (𝟙_ (pullback M'.toBase (𝟙 (Spec (CommRingCat.of k)))).Modules)) ≅ (L i).module := f
    exact ⟨c ≪≫ f'⟩

  obtain ⟨t₁⟩ := nonempty_twistL₂_iso_pf K pos neg (List.finRange n) (fun i _ => hKinv i)
  obtain ⟨pP⟩ := nonempty_pullback_listProd_module_iso gk K L hKinv hLinv em pos (List.finRange n)
  obtain ⟨pN⟩ := nonempty_pullback_listProd_module_iso gk K L hKinv hLinv em neg (List.finRange n)
  obtain ⟨t₂⟩ := nonempty_pullback_pf_iso_of_module_iso gk (isInvertible_Jp₂ K pos _ (fun i _ => hKinv i)) ⟨pP⟩ ⟨pN⟩

  let S : Finset (Place k F') := Dbar.support ∪ Finset.univ.biUnion fib
  have hsuppS : Dbar.support ⊆ S := Finset.subset_union_left
  have hfibS : ∀ i, fib i ⊆ S := fun i => (Finset.subset_biUnion_of_mem fib (Finset.mem_univ i)).trans Finset.subset_union_right
  have hinvS : ∀ v ∈ Dbar.support.toList, (placeIdeal M' v).IsInvertible := fun v _ => isInvertible_placeIdeal M' v
  obtain ⟨t₃⟩ := nonempty_twistL_iso_pf (placeIdeal M') (⇑Dbar) Dbar.support.toList hinvS
  rw [Jp_toList_eq _ Dbar S hsuppS, Jn_toList_eq _ Dbar S hsuppS] at t₃

  have hPs : ∀ (c : Place k F' → ℕ), (∏ W ∈ S, placeIdeal M' W ^ c W).IsInvertible :=
    fun c => IsInvertible.finsetProd _ S (fun W _ => (isInvertible_placeIdeal M' W).pow _)

  have hprod : ∀ (m : Fin n → ℕ), ((List.finRange n).map fun i => L i ^ m i).prod =
      ∏ W ∈ S, placeIdeal M' W ^ (∑ i, if W ∈ fib i then e W * m i else 0) := by
    intro m
    rw [← Fin.prod_univ_def]
    have h1 : ∀ i, L i ^ m i = ∏ W ∈ S, (if W ∈ fib i then placeIdeal M' W ^ (e W * m i) else 1) := by
      intro i
      have hL : L i = ∏ W ∈ fib i, placeIdeal M' W ^ e W := by simp only [L, Finset.prod_map_toList]
      rw [hL, ← Finset.prod_pow, ← Finset.prod_filter]
      have hS : S.filter (· ∈ fib i) = fib i := by
        rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hfibS i)]
      rw [hS]
      refine Finset.prod_congr rfl (fun W _ => ?_)
      rw [pow_mul]
    simp_rw [h1]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl (fun W _ => ?_)
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  have key : ((List.finRange n).map fun i => L i ^ pos i).prod * (∏ W ∈ S, placeIdeal M' W ^ (-(Dbar W)).toNat) =
      (∏ W ∈ S, placeIdeal M' W ^ (Dbar W).toNat) * ((List.finRange n).map fun i => L i ^ neg i).prod := by
    rw [hprod pos, hprod neg, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun W _ => ?_)
    rw [← pow_add, ← pow_add]
    congr 1

    have hW := hDbar W
    have hfibW : ∀ i, (W ∈ fib i ↔ M.pointEquivPlace (x i) = W.restrictAlong φ hφ) := fun i => by
      simp only [fib, Place.mem_fiberAlong]; exact eq_comm
    have hsum : (Dbar W : ℤ) = (∑ i, if W ∈ fib i then ((e W * pos i : ℕ) : ℤ) else 0) - (∑ i, if W ∈ fib i then ((e W * neg i : ℕ) : ℤ) else 0) := by
      rw [hW, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : W ∈ fib i
      · have h' : M.pointEquivPlace (x i) = W.restrictAlong φ hφ := (hfibW i).mp h
        rw [if_pos h', if_pos h, if_pos h]; push_cast; ring
      · have h' : ¬ M.pointEquivPlace (x i) = W.restrictAlong φ hφ := fun hh => h ((hfibW i).mpr hh)
        rw [if_neg h', if_neg h, if_neg h]; simp
    have hcast : ∀ (m : Fin n → ℕ), ((∑ i, if W ∈ fib i then e W * m i else 0 : ℕ) : ℤ) = ∑ i, if W ∈ fib i then ((e W * m i : ℕ) : ℤ) else 0 := by
      intro m; push_cast; refine Finset.sum_congr rfl (fun i _ => ?_); split_ifs <;> simp
    have hc1 := hcast pos
    have hc2 := hcast neg
    have h2 : ((Dbar W).toNat : ℤ) - ((-(Dbar W)).toNat : ℤ) = Dbar W := Int.toNat_sub_toNat_neg _
    omega
  have hJ' : (((List.finRange n).map fun i => L i ^ pos i).prod).IsInvertible := IsInvertible.listProd _ _ (fun i _ => (hLinv i).pow _)
  have hK' : (((List.finRange n).map fun i => L i ^ neg i).prod).IsInvertible := IsInvertible.listProd _ _ (fun i _ => (hLinv i).pow _)
  obtain ⟨c⟩ := nonempty_pf_congr hJ' (hPs _) hK' (hPs _) key
  exact ⟨(Scheme.Modules.pullback gk).mapIso t₁ ≪≫ t₂ ≪≫ c ≪≫ t₃.symm⟩

end K6H8
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong.K6H8 P2MW.S_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong.K6H8.Tw"

open AlgebraicCurve in
open Classical in

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {F : Type v} [Field F] [Algebra k F] [HasPrincipalDivisors k F] {F' : Type v} [Field F'] [Algebra k F'] [HasPrincipalDivisors k F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (g : M'.C ⟶ M.C) (hg : g ≫ M.toBase = M'.toBase)
    (hgφ : ∀ x' : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      M.pointEquivPlace ⟨x'.1 ≫ g, by rw [Category.assoc, hg]; exact x'.2⟩ = (M'.pointEquivPlace x').restrictAlong φ hφ)
    (gk : pullback M'.toBase (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback M.toBase (𝟙 (Spec (CommRingCat.of k))))
    (hgk₁ : gk ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g) (hgk₂ : gk ≫ pullback.snd _ _ = pullback.snd _ _)
    {n : ℕ} (x : Fin n → {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (pos neg : Fin n → ℕ)
    (Dbar : Divisor k F')
    (hDbar : ∀ W : Place k F', Dbar W = (Place.ramificationIndexAlong φ W : ℤ) *
      ∑ i, (if M.pointEquivPlace (x i) = W.restrictAlong φ hφ then ((pos i : ℤ) - (neg i : ℤ)) else 0)) :
    Nonempty ((Scheme.Modules.pullback gk).obj
        ((List.finRange n).foldr (fun i N =>
            ((RelEffCartierDiv.ofPoint M.toBase (x i).1 (x i).2).I ^ pos i).invModule ⊗
              ((RelEffCartierDiv.ofPoint M.toBase (x i).1 (x i).2).I ^ neg i).module ⊗ N)
          (𝟙_ (pullback M.toBase (𝟙 (Spec (CommRingCat.of k)))).Modules)) ≅
      (Dbar.support.toList).foldr (fun W N =>
          ((RelEffCartierDiv.ofPoint M'.toBase (M'.pointEquivPlace.symm W).1 (M'.pointEquivPlace.symm W).2).I ^ (Dbar W).toNat).invModule ⊗
            ((RelEffCartierDiv.ofPoint M'.toBase (M'.pointEquivPlace.symm W).1 (M'.pointEquivPlace.symm W).2).I ^ (-(Dbar W)).toNat).module ⊗ N)
        (𝟙_ (pullback M'.toBase (𝟙 (Spec (CommRingCat.of k)))).Modules)) :=
  K6H8.nonempty_pullback_twistL₂_ofPoint_iso_twist M M' φ hφ g hg hgφ gk hgk₁ hgk₂ x pos neg Dbar hDbar

end
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong.K6H8 P2MW.S_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong.K6H8.Tw"

end S_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong (solution)
