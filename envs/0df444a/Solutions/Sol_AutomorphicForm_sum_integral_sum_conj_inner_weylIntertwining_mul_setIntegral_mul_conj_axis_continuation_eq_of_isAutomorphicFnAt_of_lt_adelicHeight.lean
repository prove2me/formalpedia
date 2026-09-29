-- Prove2me | solution 1 for AutomorphicForm.sum_integral_sum_conj_inner_weylIntertwining_mul_setIntegral_mul_conj_axis_continuation_eq_of_isAutomorphicFnAt_of_lt_adelicHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/308298cf-830c-5c0c-a4af-ef65114e8473

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_AutomorphicForm_axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar
import Theorems.Thm_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
import Theorems.Thm_AutomorphicForm_exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_continuous_setIntegral_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow_of_isAutomorphicFnAt_of_lt_adelicHeight
import Theorems.Thm_AutomorphicForm_orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sum_integral_sum_conj_inner_weylIntertwining_mul_setIntegral_mul_conj_axis_continuation_eq_of_isAutomorphicFnAt_of_lt_adelicHeight
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace Ws48
namespace Axis
open Filter

theorem integral_mul_conj_of_orthonormal {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    (e : Fin n → X → ℂ) (hint : ∀ i j, Integrable (fun x => e i x * conj (e j x)) μ)
    (hon : ∀ i j, ∫ x, e i x * conj (e j x) ∂μ = if i = j then 1 else 0)
    (c : Fin n → ℂ) (w : X → ℂ) (hw : ∀ x, w x = ∑ j, c j * e j x) :
    (∀ j, ∫ x, w x * conj (e j x) ∂μ = c j) ∧
    ∫ x, w x * conj (w x) ∂μ = ∑ j, (∫ x, w x * conj (e j x) ∂μ) * conj (∫ x, w x * conj (e j x) ∂μ) := by
  have hwj : ∀ j, (fun x => w x * conj (e j x)) = fun x => ∑ i, c i * (e i x * conj (e j x)) := by
    intro j; funext x
    rw [hw x, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hintj : ∀ j, Integrable (fun x => w x * conj (e j x)) μ := by
    intro j; rw [hwj j]
    exact integrable_finsetSum _ fun i _ => (hint i j).const_mul (c i)
  have hcoef : ∀ j, ∫ x, w x * conj (e j x) ∂μ = c j := by
    intro j
    rw [hwj j, integral_finsetSum _ (fun i _ => (hint i j).const_mul (c i))]
    simp_rw [integral_const_mul, hon]
    simp
  refine ⟨hcoef, ?_⟩
  have hww : (fun x => w x * conj (w x)) = fun x => ∑ j, conj (c j) * (w x * conj (e j x)) := by
    funext x
    have : conj (w x) = ∑ j, conj (c j) * conj (e j x) := by
      rw [hw x, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul]
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hww, integral_finsetSum _ (fun j _ => (hintj j).const_mul (conj (c j)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, hcoef j, mul_comm]

section Eta
open AutomorphicForm NumberField.TateGlobal
variable (K : Type) [Field K] [NumberField K]

theorem cpowChar_mul_cpowChar (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (a b : ℂ) :
    cpowChar α hα a * cpowChar α hα b = cpowChar α hα (a + b) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.mul_apply, Units.val_mul, cpowChar_apply_val, cpowChar_apply_val, cpowChar_apply_val,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα x).ne')]

theorem cpowChar_inv (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (a : ℂ) :
    (cpowChar α hα a)⁻¹ = cpowChar α hα (-a) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, cpowChar_apply_val, cpowChar_apply_val, Complex.cpow_neg]

theorem normPowChar_eq_cpowChar (hα : ∀ x, 0 < (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ))) (τ : ℝ) :
    normPowChar K τ = cpowChar (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα (Complex.I * τ) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [coe_normPowChar_apply, cpowChar_apply_val]
  rfl

theorem etaFst_mul_normPowChar (hα : ∀ x, 0 < (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ)))
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : ℝ) (s : ℂ) :
    etaFst (μ * normPowChar K τ) (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα s =
    etaFst μ (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα (s + (τ : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  simp only [etaFst_apply, MonoidHom.mul_apply, Units.val_mul, coe_normPowChar_apply, cpowChar_apply_val]
  have hx : ((((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hα x).ne'
  have hI : ((ideleNorm K x : ℝ) : ℂ) = (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ) : ℂ) := rfl
  rw [hI, mul_assoc, ← Complex.cpow_add _ _ hx]
  congr 2; ring

theorem etaSnd_mul_normPowChar_inv (hα : ∀ x, 0 < (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ)))
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : ℝ) (s : ℂ) :
    etaSnd (ν * (normPowChar K τ)⁻¹) (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα s =
    etaSnd ν (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα (s + (τ : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  simp only [etaSnd_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    coe_normPowChar_apply, cpowChar_apply_val]
  have hx : ((((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hα x).ne'
  have hI : ((ideleNorm K x : ℝ) : ℂ) = (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ) : ℂ) := rfl
  rw [hI, ← Complex.cpow_neg, mul_assoc, ← Complex.cpow_add _ _ hx]
  congr 2; ring

end Eta

end Ws48.Axis

namespace Ws48
namespace FE2
open NumberField.TateGlobal

theorem normPowChar_add (K : Type) [Field K] [NumberField K] (a b : ℝ) :
    normPowChar K (a + b) = normPowChar K a * normPowChar K b := by
  refine MonoidHom.ext fun x => Units.ext ?_
  have hx : ((ideleNorm K x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ideleNorm_pos x).ne'
  rw [MonoidHom.mul_apply, Units.val_mul, coe_normPowChar_apply, coe_normPowChar_apply, coe_normPowChar_apply,
    ← Complex.cpow_add _ _ hx]
  congr 1
  push_cast
  ring

theorem normPowChar_neg (K : Type) [Field K] [NumberField K] (a : ℝ) :
    normPowChar K (-a) = (normPowChar K a)⁻¹ := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, coe_normPowChar_apply, coe_normPowChar_apply, ← Complex.cpow_neg]
  congr 1
  push_cast
  ring

theorem key_alg {J J' : Type} [Fintype J] [Fintype J'] {A TE' : J' → ℂ} {C TE : J → ℂ} {B : J' → J → ℂ}
    (hΘ : ∀ j', TE' j' = ∑ j, conj (B j' j) * TE j) (hC : ∀ j, ∑ j', A j' * B j' j = C j) :
    ∑ j', conj (A j') * TE' j' = ∑ j, conj (C j) * TE j := by
  have h1 : ∑ j', conj (A j') * TE' j' = ∑ j', ∑ j, conj (A j') * conj (B j' j) * TE j := by
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [hΘ j', Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j, conj (C j) * TE j = ∑ j, ∑ j', conj (A j') * conj (B j' j) * TE j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hC j, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j' _ => by rw [map_mul]
  rw [h1, h2, Finset.sum_comm]

theorem assembly {ι : Type} [Fintype ι] (r : ι → ι) (hr : Function.Involutive r) {L R : ι → ℝ → ℂ}
    (h : ∀ i t, R (r i) (-t) = L i t) : ∑ i, ∫ t, L i t = ∑ i, ∫ t, R i t := by
  calc ∑ i, ∫ t, L i t = ∑ i, ∫ t, R (r i) (-t) := by simp_rw [h]
    _ = ∑ i, ∫ t, R (r i) t := Finset.sum_congr rfl fun i _ => integral_neg_eq_self (R (r i)) volume
    _ = ∑ i, ∫ t, R i t := Equiv.sum_comp (Function.Involutive.toPerm r hr) (fun i => ∫ t, R i t)

end Ws48.FE2

end

namespace Ws48
namespace WFU
open MeasureTheory

theorem one_add_abs_add_le (t τ : ℝ) : 1 + |t + τ| ≤ (1 + |t|) * (1 + |τ|) := by
  nlinarith [abs_add_le t τ, abs_nonneg t, abs_nonneg τ]

theorem integrable_conj_mul_shift {c Θ : ℝ → ℂ} (hc : Continuous c) (hΘ : Continuous Θ)
    {m : ℝ → ℝ} (hm : Integrable m) {k : ℕ} {A D : ℝ} (τ : ℝ)
    (hcb : ∀ t, (1 + |t|) ^ k * ‖c t‖ ≤ D * m t) (hΘb : ∀ t, ‖Θ t‖ ≤ A * (1 + |t|) ^ k) :
    Integrable (fun t => (starRingEnd ℂ) (c t) * Θ (t + τ)) := by
  refine Integrable.mono' ((hm.const_mul D).const_mul (|A| * (1 + |τ|) ^ k)) ?_ ?_
  · exact ((Complex.continuous_conj.comp hc).mul (hΘ.comp (continuous_add_right τ))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    have h1 : ‖Θ (t + τ)‖ ≤ |A| * ((1 + |t|) * (1 + |τ|)) ^ k := by
      calc ‖Θ (t + τ)‖ ≤ A * (1 + |t + τ|) ^ k := hΘb _
        _ ≤ |A| * (1 + |t + τ|) ^ k := by gcongr; exact le_abs_self A
        _ ≤ |A| * ((1 + |t|) * (1 + |τ|)) ^ k := by
            have h0 : 0 ≤ 1 + |t + τ| := by positivity
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (one_add_abs_add_le t τ) k) (abs_nonneg A)
    have h2 : 0 ≤ D * m t := le_trans (by positivity) (hcb t)
    rw [norm_mul, RCLike.norm_conj]
    calc ‖c t‖ * ‖Θ (t + τ)‖ ≤ ‖c t‖ * (|A| * ((1 + |t|) * (1 + |τ|)) ^ k) := by gcongr
      _ = |A| * (1 + |τ|) ^ k * ((1 + |t|) ^ k * ‖c t‖) := by rw [mul_pow]; ring
      _ ≤ |A| * (1 + |τ|) ^ k * (D * m t) := mul_le_mul_of_nonneg_left (hcb t) (by positivity)

theorem norm_integral_mul_conj_le {X : Type*} [MeasurableSpace X] (ν : Measure X) {a b : X → ℂ}
    (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) :
    ‖∫ x, a x * (starRingEnd ℂ) (b x) ∂ν‖ ≤ (eLpNorm a 2 ν).toReal * (eLpNorm b 2 ν).toReal := by
  have h : ∫ x, a x * (starRingEnd ℂ) (b x) ∂ν = inner ℂ (hb.toLp b) (ha.toLp a) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hxa hxb
    rw [hxa, hxb, RCLike.inner_apply, mul_comm]
  rw [h, mul_comm]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [Lp.norm_toLp, Lp.norm_toLp]

theorem toReal_eLpNorm_eq_one_of_integral_mul_conj_eq_one {X : Type*} [MeasurableSpace X] (ν : Measure X) {b : X → ℂ}
    (hb : MemLp b 2 ν) (h : ∫ x, b x * (starRingEnd ℂ) (b x) ∂ν = 1) : (eLpNorm b 2 ν).toReal = 1 := by
  have h1 : ∫ x, b x * (starRingEnd ℂ) (b x) ∂ν = inner ℂ (hb.toLp b) (hb.toLp b) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hb.coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply, mul_comm]
  have h2 : (‖hb.toLp b‖ : ℝ) ^ 2 = 1 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (hb.toLp b)
    rw [← h1, h] at this
    rw [← this]; simp
  rw [← Lp.norm_toLp (f := b) (hf := hb)]
  nlinarith [norm_nonneg (hb.toLp b)]

end Ws48.WFU

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hψlev : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g)
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK)
      (u : AdelicGL2 (𝓞 K) K → ℂ)
      (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
      (_hub : ∃ T : ℝ, ∀ g ∈ AutomorphicForm.canonicalTruncationDomain K α β,
        T < NumberField.AdelicHeight.adelicHeight K g → u g = 0),
    (∀ (i : ιP) (j : Fin (nE (em i))), Integrable (fun t : ℝ =>
        conj (∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
              conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              u g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))) ∧
    (∀ (i : ιP) (j : Fin (nE (em i))), Integrable (fun t : ℝ =>
        conj (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              u g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))) ∧
    (∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
        conj (∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
              conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              u g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) =
      ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
        conj (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              u g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _ μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP _ μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty u hu hub
  letI := adeleBorel (𝓞 K) K
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  have hNbot : N ≠ ⊥ := by
    intro hN0
    have hall : ∀ w : HeightOneSpectrum (𝓞 K), w ∈ SK := fun w => hN w (by
      rw [hN0, ← Ideal.zero_eq_bot]; exact dvd_zero _)
    have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int _
    have key : ∀ p : {p : ℕ // p.Prime}, ∃ w : HeightOneSpectrum (𝓞 K),
        w.asIdeal.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : ℤ)} := by
      intro p
      have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast p.2.ne_zero
      haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime hp0).2 (Nat.prime_iff_prime_int.1 p.2)
      obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {((p : ℕ) : ℤ)})
        (⊥ : Ideal (𝓞 K)) (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
      have hQ0 : Q ≠ ⊥ := by
        intro h
        rw [h, Ideal.comap_bot_of_injective _ hinj] at hQc
        exact hp0 (Ideal.span_singleton_eq_bot.1 hQc.symm)
      exact ⟨⟨Q, hQ, hQ0⟩, hQc⟩
    choose f hf using key
    have hfinj : Function.Injective f := by
      intro p q hpq
      have h := hf p
      rw [hpq, hf q, Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h
      exact Subtype.ext (by simpa using h.symm)
    haveI : Infinite {p : ℕ // p.Prime} := Nat.infinite_setOf_prime.to_subtype
    exact (Set.infinite_of_injective_forall_mem hfinj (fun p => (Finset.mem_coe.2 (hall (f p)))))
      (Finset.finite_toSet SK)

  have hEcont : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s : ℂ), s ∈ OE e₀ j₀ → Continuous fun x : AdelicGL2 (𝓞 K) K => EE e₀ j₀ s x := by
    intro e₀ j₀ s hs
    exact ((_hEE e₀ j₀).2.2.2.2.2.2.1).comp_continuous (Continuous.prodMk continuous_const continuous_id)
      (fun x => ⟨hs, Set.mem_univ _⟩)

  have hint_u : ∀ (F : AdelicGL2 (𝓞 K) K → ℂ), Continuous F →
      Integrable (fun g : AdelicGL2 (𝓞 K) K => u g * conj (F g))
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
    intro F hF
    obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
    have hfin : (adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β) < ⊤ := by
      have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ
        (AutomorphicForm.canonicalTruncationDomain K α β) hFD
      rwa [Set.inter_eq_left.mpr hslab] at h
    haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
      isFiniteMeasure_restrict.2 hfin.ne
    have haeΦ : ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)),
        g ∈ AutomorphicForm.canonicalTruncationDomain K α β := by
      have hre : ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
            {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}).restrict
            (AutomorphicForm.canonicalTruncationDomain K α β) =
          (adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β) := by
        rw [Measure.restrict_restrict₀ hFD.nullMeasurableSet, Set.inter_eq_left.mpr hslab]
      rw [← hre]
      exact ae_restrict_mem₀ hFD.nullMeasurableSet
    obtain ⟨T, hT⟩ := hub
    obtain ⟨C, hC, hsub⟩ := AutomorphicForm.exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset K α β hα hαβ T
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
    have hu2 : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
      ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu).2
    have hu1 : Integrable u ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
      hu2.integrable one_le_two
    refine Integrable.mono' (hu1.norm.const_mul M) ?_ ?_
    · exact hu2.aestronglyMeasurable.mul (Complex.continuous_conj.comp hF).aestronglyMeasurable
    · filter_upwards [haeΦ] with g hg
      rw [norm_mul, RCLike.norm_conj]
      by_cases hle : NumberField.AdelicHeight.adelicHeight K g ≤ T
      · have hgC : g ∈ C := hsub ⟨hg, hle⟩
        calc ‖u g‖ * ‖F g‖ ≤ ‖u g‖ * M := by gcongr; exact hM g hgC
          _ = M * ‖u g‖ := mul_comm _ _
      · have h0 : u g = 0 := hT g hg (lt_of_not_ge hle)
        simp [h0]
  have hTS : ∀
      (e ē : ιE) (σ : ℝ)
      (_hsw : μ ē = ν e * NumberField.TateGlobal.normPowChar K σ ∧
        ν ē = μ e * (NumberField.TateGlobal.normPowChar K σ)⁻¹)
      (j : Fin (nE e)) (t : ℝ),
      (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      ∑ j' : Fin (nE ē),
        conj (∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
              NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
            conj (φE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
    intro e ē σ _hsw j t
    have hmem_e : ((t : ℂ) * Complex.I) ∈ OE e j := (_hEE e j).2.2.1 (by simp)
    have hmem_ē : ∀ j', (-((((t + σ : ℝ) : ℂ)) * Complex.I)) ∈ OE ē j' := fun j' => (_hEE ē j').2.2.1 (by simp)
    have hFE := AutomorphicForm.axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar
      K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm
      ι b cls hb hbn hbo hbs hbc ιE μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol
      _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE e ē σ _hsw j t
    have hint : ∀ j' : Fin (nE ē), Integrable (fun g : AdelicGL2 (𝓞 K) K => u g * conj (EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g))
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := fun j' =>
      hint_u _ (hEcont ē j' _ (hmem_ē j'))
    have hpt : (fun g : AdelicGL2 (𝓞 K) K => u g * conj (EE e j ((t : ℂ) * Complex.I) g)) =
        fun g => ∑ j' : Fin (nE ē), conj (∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
              NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
            conj (φE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          (u g * conj (EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g)) := by
      funext g
      rw [hFE g, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [map_mul]; ring
    show (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = _
    rw [hpt, integral_finsetSum _ (fun j' _ => (hint j').const_mul _)]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [integral_const_mul]

  have hKc : IsCompact ((adelicMaximalCompact K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) := by
    have := isCompact_univ.image (continuous_subtype_val : Continuous (fun k : ↥(adelicMaximalCompact K) => (k : AdelicGL2 (𝓞 K) K)))
    rwa [Set.image_univ, Subtype.range_coe] at this
  have hG : ∀ (i : ιP) (j : Fin (nE (em i))),
      (Continuous fun t : ℝ => ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          u g * conj (EE (em i) j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
      ∃ (A : ℝ) (k : ℕ), ∀ t : ℝ, ‖∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          u g * conj (EE (em i) j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ k :=
    fun i j => AutomorphicForm.continuous_setIntegral_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow_of_isAutomorphicFnAt_of_lt_adelicHeight K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE u hu hub (em i) j

  have hφc : ∀ (e₀ : ιE) (j' : Fin (nE e₀)) (s : ℂ), Continuous fun k : adelicMaximalCompact K => φE e₀ j' s (k : AdelicGL2 (𝓞 K) K) :=
    fun e₀ j' s => ((_hφEjc e₀ j').comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val
  have hNEc : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)), Continuous fun p : ℝ × ↥(adelicMaximalCompact K) =>
      NE e₀ j₀ ((((p.1 : ℝ) : ℂ)) * Complex.I) (p.2 : AdelicGL2 (𝓞 K) K) := by
    intro e₀ j₀
    have hax : ∀ t : ℝ, ((t : ℂ) * Complex.I) ∈ OE e₀ j₀ := fun t => (_hEE e₀ j₀).2.2.1 (by simp)
    refine ((_hEE e₀ j₀).2.2.2.2.2.2.2.1).comp_continuous (f := fun p : ℝ × ↥(adelicMaximalCompact K) => ((((p.1 : ℝ) : ℂ)) * Complex.I, (p.2 : AdelicGL2 (𝓞 K) K))) ?_ (fun p => ⟨hax p.1, Set.mem_univ _⟩)
    exact Continuous.prodMk ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const) (continuous_subtype_val.comp continuous_snd)
  refine ⟨?_, ?_, ?_⟩
  ·
    intro i j
    obtain ⟨hΘc, A, k, hΘ⟩ := hG i j
    obtain ⟨m, hm, -, hmb⟩ := _hψdec (rP i) k 0 _ hKc
    have hmb0 := hmb 0 (by simp)

    set c2 : ℝ → ℂ := fun t => ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
        conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) with hc2
    have hc2c : Continuous c2 := by
      have hunc : Continuous (Function.uncurry fun (t : ℝ) (k' : ↥(adelicMaximalCompact K)) => ψf (rP i) (-((t : ℂ) * Complex.I)) (k' : AdelicGL2 (𝓞 K) K) *
          conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))) := by
        refine Continuous.mul ?_ (Complex.continuous_conj.comp (continuous_const.mul ?_))
        · exact (_hψjc (rP i)).comp (Continuous.prodMk (((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).neg) (continuous_subtype_val.comp continuous_snd))
        · exact (hNEc (em i) j).comp (Continuous.prodMk (continuous_fst.add continuous_const) continuous_snd)
      have := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar K) hunc isCompact_univ
      simpa only [Measure.restrict_univ] using this

    have hvN := fun t : ℝ => (AutomorphicForm.orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
      K N tysK hαm (μ (em i)) (ν (em i)) (_hμE (em i)) (_hνE (em i)) (_hμicE (em i)) (_hνicE (em i)) (_hμcE (em i)) (_hνcE (em i))
      (nE (em i)) (φE (em i)) (_hφE (em i)) (_hφEK (em i)) (_hφEf (em i)) (_hφEjc (em i)) (_hφEhol (em i)) (_hφEKu (em i))
      (_hφEflat (em i)) (_hφElev (em i)) (_hφEty (em i)) (_hφEon (em i)) (OE (em i)) (EE (em i)) (NE (em i)) (_hEE (em i)) t)
    have hcb : ∀ t : ℝ, (1 + |t|) ^ k * ‖c2 t‖ ≤ 1 * m (-t) := by
      intro t
      set a : adelicMaximalCompact K → ℂ := fun k' => (((1 + |t|) ^ k : ℝ) : ℂ) * ψf (rP i) (-((t : ℂ) * Complex.I)) (k' : AdelicGL2 (𝓞 K) K) with ha
      set bN : adelicMaximalCompact K → ℂ := fun k' => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) with hbN
      have hac : Continuous a := continuous_const.mul (((_hψjc (rP i)).comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val)
      have hbc : Continuous bN :=
        continuous_const.mul ((hNEc (em i) j).comp (Continuous.prodMk (continuous_const (y := t + τ i)) continuous_id))
      have ha2 : MemLp a 2 (maximalCompactHaar K) := (hac.memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) _).mono_exponent le_top
      have hb2 : MemLp bN 2 (maximalCompactHaar K) := (hbc.memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) _).mono_exponent le_top

      have hb1 : (eLpNorm bN 2 (maximalCompactHaar K)).toReal = 1 := by
        refine Ws48.WFU.toReal_eLpNorm_eq_one_of_integral_mul_conj_eq_one _ hb2 ?_
        have h := (hvN (t + τ i)).1 j j
        simp only [if_true] at h
        exact h

      have hmt : 0 ≤ m (-t) := le_trans (by positivity) (hmb0 (-t) (1 : AdelicGL2 (𝓞 K) K) (one_mem _))
      have ha1 : (eLpNorm a 2 (maximalCompactHaar K)).toReal ≤ m (-t) := by
        have hbound : ∀ᵐ k' ∂(maximalCompactHaar K), ‖a k'‖ ≤ m (-t) := by
          refine Filter.Eventually.of_forall fun k' => ?_
          rw [ha, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + |t|) ^ k)]
          have := hmb0 (-t) (k' : AdelicGL2 (𝓞 K) K) k'.2
          have e0 : (((0 : ℝ) : ℂ)) + (((-t : ℝ) : ℂ)) * Complex.I = -((t : ℂ) * Complex.I) := by push_cast; ring
          rwa [abs_neg, e0] at this
        have h := eLpNorm_le_of_ae_bound (p := 2) hbound
        simp only [measure_univ, ENNReal.one_rpow, one_mul] at h
        have hne : eLpNorm a 2 (maximalCompactHaar K) ≠ ⊤ := ha2.eLpNorm_ne_top
        calc (eLpNorm a 2 (maximalCompactHaar K)).toReal ≤ (ENNReal.ofReal (m (-t))).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
          _ = m (-t) := ENNReal.toReal_ofReal hmt
      have hCS := Ws48.WFU.norm_integral_mul_conj_le (maximalCompactHaar K) ha2 hb2
      have heq : (((1 + |t|) ^ k : ℝ) : ℂ) * c2 t = ∫ k', a k' * conj (bN k') ∂(maximalCompactHaar K) := by
        rw [hc2, ← integral_const_mul]
        congr 1; funext k'; simp only [ha, hbN]; ring
      have hpos : (0 : ℝ) ≤ (1 + |t|) ^ k := by positivity
      have hnorm : ‖(((1 + |t|) ^ k : ℝ) : ℂ)‖ = (1 + |t|) ^ k := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
      calc (1 + |t|) ^ k * ‖c2 t‖ = ‖(((1 + |t|) ^ k : ℝ) : ℂ) * c2 t‖ := by rw [norm_mul, hnorm]
        _ = ‖∫ k', a k' * conj (bN k') ∂(maximalCompactHaar K)‖ := by rw [heq]
        _ ≤ (eLpNorm a 2 (maximalCompactHaar K)).toReal * (eLpNorm bN 2 (maximalCompactHaar K)).toReal := hCS
        _ ≤ m (-t) * 1 := by rw [hb1]; exact mul_le_mul_of_nonneg_right ha1 zero_le_one
        _ = 1 * m (-t) := by ring
    exact Ws48.WFU.integrable_conj_mul_shift hc2c hΘc hm.comp_neg (τ i) hcb hΘ
  ·
    intro i j
    obtain ⟨hΘc, A, k, hΘ⟩ := hG i j
    obtain ⟨m, hm, -, hmb⟩ := _hψdec i k 0 _ hKc
    have hmb0 := hmb 0 (by simp)
    set c1 : ℝ → ℂ := fun t => ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) with hc1
    have hc1c : Continuous c1 := by
      have hunc : Continuous (Function.uncurry fun (t : ℝ) (k' : ↥(adelicMaximalCompact K)) => ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
          conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))) := by
        refine Continuous.mul ?_ (Complex.continuous_conj.comp ?_)
        · exact (_hψjc i).comp (Continuous.prodMk ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const) (continuous_subtype_val.comp continuous_snd))
        · exact (_hφEjc (em i) j).comp (Continuous.prodMk (((Complex.continuous_ofReal.comp (continuous_fst.add continuous_const))).mul continuous_const) (continuous_subtype_val.comp continuous_snd))
      have := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar K) hunc isCompact_univ
      simpa only [Measure.restrict_univ] using this
    set I₀ : ℝ := ∫ k', ‖φE (em i) j 0 (k' : AdelicGL2 (𝓞 K) K)‖ ∂(maximalCompactHaar K) with hI₀
    have hφint : Integrable (fun k' : adelicMaximalCompact K => ‖φE (em i) j 0 (k' : AdelicGL2 (𝓞 K) K)‖) (maximalCompactHaar K) :=
      ((hφc (em i) j 0).norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hcb : ∀ t : ℝ, (1 + |t|) ^ k * ‖c1 t‖ ≤ I₀ * m t := by
      intro t
      have hmt : 0 ≤ m t := le_trans (by positivity) (hmb0 t (1 : AdelicGL2 (𝓞 K) K) (one_mem _))
      have hpt : ∀ k' : adelicMaximalCompact K,
          (1 + |t|) ^ k * ‖ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))‖ ≤
          m t * ‖φE (em i) j 0 (k' : AdelicGL2 (𝓞 K) K)‖ := by
        intro k'
        rw [norm_mul, RCLike.norm_conj, _hφEflat (em i) j _ k', ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have := hmb0 t (k' : AdelicGL2 (𝓞 K) K) k'.2
        have e0 : (((0 : ℝ) : ℂ)) + ((t : ℝ) : ℂ) * Complex.I = (t : ℂ) * Complex.I := by push_cast; ring
        rwa [e0] at this
      have hint1 : Integrable (fun k' : adelicMaximalCompact K => ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
        ((((_hψjc i).comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val).mul
          (Complex.continuous_conj.comp (hφc (em i) j _))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      calc (1 + |t|) ^ k * ‖c1 t‖ ≤ (1 + |t|) ^ k * ∫ k', ‖ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))‖ ∂(maximalCompactHaar K) := by
              rw [hc1]; exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
        _ = ∫ k', (1 + |t|) ^ k * ‖ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))‖ ∂(maximalCompactHaar K) := (integral_const_mul _ _).symm
        _ ≤ ∫ k', m t * ‖φE (em i) j 0 (k' : AdelicGL2 (𝓞 K) K)‖ ∂(maximalCompactHaar K) :=
              integral_mono (hint1.norm.const_mul _) (hφint.const_mul _) hpt
        _ = I₀ * m t := by rw [integral_const_mul, hI₀, mul_comm]
    exact Ws48.WFU.integrable_conj_mul_shift hc1c hΘc hm (τ i) hcb hΘ
  have hrr : Function.Involutive rP := by
    intro i
    by_contra hne
    obtain ⟨x, -, hx⟩ := _hdistP (rP (rP i)) i hne
    rw [(_hr (rP i)).1, (_hr i).2, (_hr (rP i)).2, (_hr i).1] at hx
    exact hx.elim (fun h => h rfl) (fun h => h rfl)
  have hφc : ∀ (e₀ : ιE) (j' : Fin (nE e₀)) (s : ℂ), Continuous fun k : adelicMaximalCompact K => φE e₀ j' s (k : AdelicGL2 (𝓞 K) K) :=
    fun e₀ j' s => ((_hφEjc e₀ j').comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val
  refine Ws48.FE2.assembly rP hrr ?_
  intro i t
  beta_reduce
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = -(τ i + τ (rP i)) := ⟨_, rfl⟩
  have e1 : ((-t : ℝ) : ℂ) * Complex.I = (-((t : ℂ) * Complex.I)) := by push_cast; ring
  have e2 : -((((-t + τ (rP i) + σ : ℝ) : ℂ)) * Complex.I) = ((((t + τ i : ℝ) : ℂ)) * Complex.I) := by rw [hσ]; push_cast; ring
  rw [e1]

  have hsw : μ (em i) = ν (em (rP i)) * NumberField.TateGlobal.normPowChar K σ ∧
      ν (em i) = μ (em (rP i)) * (NumberField.TateGlobal.normPowChar K σ)⁻¹ := by
    obtain ⟨h1, h2⟩ := _hem i
    obtain ⟨h3, h4⟩ := _hem (rP i)
    obtain ⟨h5, h6⟩ := _hr i
    constructor
    · refine MonoidHom.ext fun x => ?_
      have a1 := DFunLike.congr_fun h1 x
      have a4 := DFunLike.congr_fun h4 x
      have a6 := DFunLike.congr_fun h6 x
      rw [MonoidHom.mul_apply] at a1 a4 ⊢
      rw [MonoidHom.inv_apply] at a4
      rw [hσ, Ws48.FE2.normPowChar_neg, Ws48.FE2.normPowChar_add, MonoidHom.inv_apply, MonoidHom.mul_apply]
      have h7 : μ (em i) x = μP i x * (NumberField.TateGlobal.normPowChar K (τ i) x)⁻¹ := by
        rw [a1, mul_inv_cancel_right]
      rw [h7, ← a6, a4, mul_inv, mul_assoc, mul_comm ((NumberField.TateGlobal.normPowChar K (τ (rP i)) x)⁻¹)]
    · refine MonoidHom.ext fun x => ?_
      have a2 := DFunLike.congr_fun h2 x
      have a3 := DFunLike.congr_fun h3 x
      have a5 := DFunLike.congr_fun h5 x
      rw [MonoidHom.mul_apply] at a2 a3 ⊢
      rw [MonoidHom.inv_apply] at a2 ⊢
      rw [hσ, Ws48.FE2.normPowChar_neg, MonoidHom.inv_apply, inv_inv, Ws48.FE2.normPowChar_add, MonoidHom.mul_apply]
      have h7 : ν (em i) x = νP i x * NumberField.TateGlobal.normPowChar K (τ i) x := by
        rw [a2, inv_mul_cancel_right]
      rw [h7, ← a5, a3, mul_assoc, mul_comm (NumberField.TateGlobal.normPowChar K (τ (rP i)) x)]

  have hTSi := fun j' : Fin (nE (em (rP i))) => hTS (em (rP i)) (em i) σ hsw j' (-t + τ (rP i))
  rw [e2] at hTSi
  apply Ws48.FE2.key_alg (B := fun (j' : Fin (nE (em (rP i)))) (j : Fin (nE (em i))) =>
      ∫ k, (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) hTSi
  intro j
  beta_reduce

  have hψind : IsInducedSection (𝓞 K) K (etaFst (μ (em (rP i))) αm hαm ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I)) (etaSnd (ν (em (rP i))) αm hαm ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I)) (ψf (rP i) (-((t : ℂ) * Complex.I))) := by
    have h := _hψf (rP i) (-((t : ℂ) * Complex.I))
    rw [(_hem (rP i)).1, (_hem (rP i)).2, Ws48.Axis.etaFst_mul_normPowChar K hαm,
      Ws48.Axis.etaSnd_mul_normPowChar_inv K hαm] at h
    have e3 : (-((t : ℂ) * Complex.I)) + ((τ (rP i) : ℝ) : ℂ) * Complex.I = ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) := by push_cast; ring
    rwa [e3] at h
  have hψc : Continuous (ψf (rP i) (-((t : ℂ) * Complex.I))) := (_hψjc (rP i)).comp (Continuous.prodMk continuous_const continuous_id)
  have hspan := _hφEspan (em (rP i)) (-t + τ (rP i)) _ hψind hψc (_hψK (rP i) _) (fun g u hu => _hψlev (rP i) _ g u hu) (_hψty (rP i) _)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hspan
  have hψs : ∀ k : adelicMaximalCompact K, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) = ∑ j', c j' * φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K) := by
    intro k
    have := congrFun hc (k : AdelicGL2 (𝓞 K) K)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hψ0 : ∀ k : adelicMaximalCompact K, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) = ∑ j', c j' * φE (em (rP i)) j' 0 (k : AdelicGL2 (𝓞 K) K) := by
    intro k
    rw [hψs k]
    exact Finset.sum_congr rfl fun j' _ => by rw [_hφEflat (em (rP i)) j' _ k]
  have hint0 : ∀ i' j', Integrable (fun k : adelicMaximalCompact K => φE (em (rP i)) i' 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE (em (rP i)) j' 0 (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
    fun i' j' => ((hφc (em (rP i)) i' 0).mul (Complex.continuous_conj.comp (hφc (em (rP i)) j' 0))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨hcoef, -⟩ := Ws48.Axis.integral_mul_conj_of_orthonormal (maximalCompactHaar K)
    (fun j' (k : adelicMaximalCompact K) => φE (em (rP i)) j' 0 (k : AdelicGL2 (𝓞 K) K)) hint0 (_hφEon (em (rP i))) c _ hψ0
  have hA : ∀ j' : Fin (nE (em (rP i))), (∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = c j' := by
    intro j'
    rw [← hcoef j']
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [_hφEflat (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) k]

  have hmemI : ((((t + τ i : ℝ) : ℂ)) * Complex.I) ∈ OE (em i) j := (_hEE (em i) j).2.2.1 (by simp)
  have hWc : Continuous fun g : AdelicGL2 (𝓞 K) K => NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g :=
    ((_hEE (em i) j).2.2.2.2.2.2.2.1).comp_continuous (Continuous.prodMk continuous_const continuous_id)
      (fun x => ⟨hmemI, Set.mem_univ _⟩)
  have hB : ∀ j' : Fin (nE (em (rP i))),
      (∫ k, (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
        ∫ k, φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    intro j'
    obtain ⟨cσ, hcσ⟩ : ∃ c₀ : ℂ, c₀ = -((σ : ℂ) * Complex.I) := ⟨_, rfl⟩
    obtain ⟨hOo, hOpc, hOax, hOhalf, hEan, hNan, hEc, hNc, hEeq, hNeq⟩ := _hEE (em i) j
    have hψ2 : ∀ s, IsInducedSection (𝓞 K) K (etaFst (ν (em (rP i))) αm hαm s) (etaSnd (μ (em (rP i))) αm hαm s)
        (fun g : AdelicGL2 (𝓞 K) K => φE (em i) j (s + cσ) g) := fun s => by
      have h := _hφE (em i) j (s + cσ)
      rw [hsw.1, hsw.2, Ws48.Axis.etaFst_mul_normPowChar K hαm, Ws48.Axis.etaSnd_mul_normPowChar_inv K hαm] at h
      have e5 : s + cσ + (σ : ℂ) * Complex.I = s := by rw [hcσ]; ring
      rw [e5] at h
      exact h
    have hψ2jc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE (em i) j (p.1 + cσ) p.2) :=
      (_hφEjc (em i) j).comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
    have hψ2hol : ∀ g : AdelicGL2 (𝓞 K) K, Differentiable ℂ (fun s => φE (em i) j (s + cσ) g) := fun g =>
      (_hφEhol (em i) j g).comp (differentiable_id.add_const _)
    have hψ2Ku : ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE (em i) j (s + cσ) (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W := fun w => by
      obtain ⟨W, h1, h2⟩ := _hφEKu (em i) j w
      exact ⟨W, h1, fun s g => h2 _ g⟩
    let eτ : ℂ ≃ₜ ℂ := Homeomorph.addRight cσ
    have hre : ∀ s : ℂ, (s + cσ).re = s.re := fun s => by simp [hcσ]
    have hEψ : IsOpen (eτ ⁻¹' OE (em i) j) ∧ IsPreconnected (eτ ⁻¹' OE (em i) j) ∧ {s : ℂ | s.re = 0} ⊆ (eτ ⁻¹' OE (em i) j) ∧
        {s : ℂ | 1 / 2 < s.re} ⊆ (eτ ⁻¹' OE (em i) j) ∧
        (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE (em i) j (s + cσ) g) (eτ ⁻¹' OE (em i) j)) ∧
        (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE (em i) j (s + cσ) g) (eτ ⁻¹' OE (em i) j)) ∧
        ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE (em i) j (p.1 + cσ) p.2) ((eτ ⁻¹' OE (em i) j) ×ˢ Set.univ) ∧
        ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE (em i) j (p.1 + cσ) p.2) ((eτ ⁻¹' OE (em i) j) ×ˢ Set.univ) ∧
        (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
          EE (em i) j (s + cσ) g = φE (em i) j (s + cσ) g + ∑' ξ : K, φE (em i) j (s + cσ) (adelicWeyl (𝓞 K) K
            * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
        (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
          NE (em i) j (s + cσ) g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (fun g : AdelicGL2 (𝓞 K) K => φE (em i) j (s + cσ) g) g) := by
      have hmem : ∀ s : ℂ, s ∈ eτ ⁻¹' OE (em i) j ↔ s + cσ ∈ OE (em i) j := fun s => Iff.rfl
      refine ⟨eτ.isOpen_preimage.2 hOo, eτ.isPreconnected_preimage.2 hOpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro s hs; exact (hmem s).2 (hOax (by simp only [Set.mem_setOf_eq] at hs ⊢; rw [hre, hs]))
      · intro s hs; exact (hmem s).2 (hOhalf (by simp only [Set.mem_setOf_eq] at hs ⊢; rw [hre]; exact hs))
      · intro g
        exact (hEan g).comp (analyticOnNhd_id.add analyticOnNhd_const) (fun s hs => hs)
      · intro g
        exact (hNan g).comp (analyticOnNhd_id.add analyticOnNhd_const) (fun s hs => hs)
      · refine hEc.comp (((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn) ?_
        intro p hp; exact ⟨hp.1, Set.mem_univ _⟩
      · refine hNc.comp (((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn) ?_
        intro p hp; exact ⟨hp.1, Set.mem_univ _⟩
      · intro s hs g; exact hEeq (s + cσ) (by rw [hre]; exact hs) g
      · intro s hs g; exact hNeq (s + cσ) (by rw [hre]; exact hs) g
    have h4 := AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
      K N hNbot hαm (μ (em (rP i))) (ν (em (rP i))) (_hμE (em (rP i))) (_hνE (em (rP i))) (_hμicE (em (rP i))) (_hνicE (em (rP i))) (_hμcE (em (rP i))) (_hνcE (em (rP i)))
      (φE (em (rP i)) j') (_hφE (em (rP i)) j') (_hφEK (em (rP i)) j') (_hφEf (em (rP i)) j') (_hφEjc (em (rP i)) j') (_hφEhol (em (rP i)) j') (_hφEKu (em (rP i)) j')
      (_hφElev (em (rP i)) j')
      (fun s (g : AdelicGL2 (𝓞 K) K) => φE (em i) j (s + cσ) g) hψ2 (fun s => _hφEK (em i) j _) (fun s => _hφEf (em i) j _) hψ2jc hψ2hol hψ2Ku
      (fun s g u hu => _hφElev (em i) j _ g u hu)
      (OE (em (rP i)) j') (EE (em (rP i)) j') (NE (em (rP i)) j') (_hEE (em (rP i)) j')
      (eτ ⁻¹' OE (em i) j) (fun s g => EE (em i) j (s + cσ) g) (fun s g => NE (em i) j (s + cσ) g) hEψ (-t + τ (rP i))
    have e4 : -(((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I)) + cσ = ((((t + τ i : ℝ) : ℂ)) * Complex.I) := by rw [hcσ, hσ]; push_cast; ring
    simp only [e4] at h4
    exact h4.symm

  have hintW : ∀ j' : Fin (nE (em (rP i))), Integrable (fun k : adelicMaximalCompact K =>
      φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) := fun j' =>
    ((hφc (em (rP i)) j' _).mul (Complex.continuous_conj.comp ((continuous_const.mul hWc).comp continuous_subtype_val))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc _ = ∑ j' : Fin (nE (em (rP i))), c j' * ∫ k, φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) :=
        Finset.sum_congr rfl fun j' _ => by rw [hA j', hB j']
    _ = ∑ j' : Fin (nE (em (rP i))), ∫ k, c j' * (φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K) :=
        Finset.sum_congr rfl fun j' _ => (integral_const_mul _ _).symm
    _ = ∫ k, ∑ j' : Fin (nE (em (rP i))), c j' * (φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K) :=
        (integral_finsetSum _ fun j' _ => (hintW j').const_mul _).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun k => by
        rw [hψs k, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j' _ => by ring)

end S_AutomorphicForm_sum_integral_sum_conj_inner_weylIntertwining_mul_setIntegral_mul_conj_axis_continuation_eq_of_isAutomorphicFnAt_of_lt_adelicHeight
end P2MW
export P2MW.S_AutomorphicForm_sum_integral_sum_conj_inner_weylIntertwining_mul_setIntegral_mul_conj_axis_continuation_eq_of_isAutomorphicFnAt_of_lt_adelicHeight (solution)
