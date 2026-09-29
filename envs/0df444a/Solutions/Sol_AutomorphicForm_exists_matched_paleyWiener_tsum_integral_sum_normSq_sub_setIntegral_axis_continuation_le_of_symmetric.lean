-- Prove2me | solution 1 for AutomorphicForm.exists_matched_paleyWiener_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le_of_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3cf1b2e9-81d8-58f9-a690-09dc17702d13

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
import Theorems.Thm_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport
import Theorems.Thm_MeasureTheory_memLp_two_and_integral_sum_norm_sq_sub_le_mul_add_of_eq_mul_add_sum_conj_mul_of_bessel
import Theorems.Thm_AutomorphicForm_sum_norm_sq_sum_conj_inner_weylIntertwining_mul_le_sum_norm_sq_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_exists_matched_paleyWiener_injective_and_inner_eq_integral_mul_cexp_and_sum_integral_sum_conj_inner_mul_eq_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport
import Theorems.Thm_MeasureTheory_exists_contDiff_hasCompactSupport_integral_normSq_sub_integral_mul_cexp_lt_of_memLp_two
import Theorems.Thm_AutomorphicForm_inner_weylIntertwining_eq_sum_inner_mul_conj_inner_of_matched_paleyWiener
import Theorems.Thm_MeasureTheory_sum_norm_sq_sum_conj_integral_mul_conj_mul_le_sum_norm_sq_of_orthonormal
import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_matched_paleyWiener_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le_of_symmetric
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

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

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm
open scoped ENNReal

set_option maxHeartbeats 4000000 in
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
      (F : (e : ιE) → Fin (nE e) → ℝ → ℂ)
      (_hF2 : ∀ (e : ιE) (j : Fin (nE e)), MemLp (F e j) 2)
      (_hFs : Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖F e j t‖ ^ 2))
      (_hFsym : ∀ (e ē : ιE) (σ : ℝ),
        (μ ē = ν e * NumberField.TateGlobal.normPowChar K σ ∧
          ν ē = μ e * (NumberField.TateGlobal.normPowChar K σ)⁻¹) →
        ∀ (j : Fin (nE e)) (t : ℝ),
          F e j t = ∑ j' : Fin (nE ē),
            conj (∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
                  NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
                conj (φE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
              F ē j' (-(t + σ)))
      (ε : ℝ) (_hε : 0 < ε),
    ∃ (ιP : Type) (_instP : Fintype ιP)
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
      (pψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pψ)
      (_hpψc : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (pψ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpψo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0),
    (∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ =>
        F e j t - (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) 2) ∧
    Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e),
        ‖F e j t - (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2) ∧
    ∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e),
        ‖F e j t - (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2 ≤ ε ^ 2 := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _instC μ ν hμu hνu hμic hνic hμc hνc hμν hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE F hF2 hFs hFsym ε hε
  classical
  letI hMSA : MeasurableSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.adeleBorel (𝓞 K) K
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K

  obtain ⟨κ, hκ, hCP⟩ := AutomorphicForm.exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm
  obtain ⟨CR, hCR, hVAL⟩ := AutomorphicForm.exists_matched_paleyWiener_injective_and_inner_eq_integral_mul_cexp_and_sum_integral_sum_conj_inner_mul_eq_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm

  set a : ιE → ℝ := fun e => ∫ t : ℝ, ∑ j : Fin (nE e), ‖F e j t‖ ^ 2 with ha
  have ha0 : ∀ e, 0 ≤ a e := fun e => integral_nonneg fun t => Finset.sum_nonneg fun j _ => by positivity
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : Finset ιE, ∑' e : {e : ιE // e ∉ F₀}, a e < ε ^ 2 / 8 := by
    have h := tendsto_tsum_compl_atTop_zero a
    have h8 : (0 : ℝ) < ε ^ 2 / 8 := by positivity
    obtain ⟨s, hs⟩ := (h.eventually (gt_mem_nhds h8)).exists_forall_of_atTop
    exact ⟨s, hs s le_rfl⟩

  set M₀ : ℕ := ∑ e ∈ F₀, nE e with hM₀
  have hδ : (0 : ℝ) < ε ^ 2 / (16 * κ ^ 2 * (M₀ + 1)) := by positivity
  have hdata : ∀ (e : ιE) (j : Fin (nE e)), ∃ hh : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) hh ∧ HasCompactSupport hh ∧
      MemLp (fun t : ℝ => (∫ x : ℝ, hh x * Complex.exp (((t : ℝ) : ℂ) * Complex.I * (x : ℂ)))) 2 ∧
      ∫ t : ℝ, ‖(((2 * κ)⁻¹ : ℝ) : ℂ) * F e j t - (∫ x : ℝ, hh x * Complex.exp (((t : ℝ) : ℂ) * Complex.I * (x : ℂ)))‖ ^ 2 < ε ^ 2 / (16 * κ ^ 2 * (M₀ + 1)) :=
    fun e j => MeasureTheory.exists_contDiff_hasCompactSupport_integral_normSq_sub_integral_mul_cexp_lt_of_memLp_two _ ((hF2 e j).const_mul _) _ hδ
  choose hh hhC hhS hhL hhδ using hdata
  set h : (e : ιE) → Fin (nE e) → ℝ → ℂ := fun e j => if e ∈ F₀ then hh e j else 0 with hhdef
  have hh1 : ∀ (e : ιE) (j : Fin (nE e)), ContDiff ℝ (⊤ : ℕ∞) (h e j) ∧ HasCompactSupport (h e j) := by
    intro e j
    by_cases he : e ∈ F₀
    · simp only [hhdef, he, if_true]; exact ⟨hhC e j, hhS e j⟩
    · simp only [hhdef, he, if_false]; exact ⟨contDiff_const, HasCompactSupport.zero⟩
  have hh2 : ∀ e : ιE, e ∉ F₀ → ∀ j : Fin (nE e), h e j = 0 := by
    intro e he j; simp only [hhdef, he, if_false]

  obtain ⟨ιP, instP, μP, νP, hμP, hνP, hμicP, hνicP, hμcP, hμνP, rP, hr, hdistP, ψf, hψf, hψjc, hψhol, hψK, hψsm, hψKu, hνcP, hψdec, ψ, hψ, hψrep, em, τ, hem, hψlev, hψty, pψ, hpψ, hpψc, hpψo, hinj, hcov, hV1, -, hnorm⟩ := hVAL ι b cls hb hbn hbo hbs hbc ιE μ ν hμu hνu hμic hνic hμc hνc hμν hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE F₀ h hh1 hh2
  have hC := hCP ι b cls hb hbn hbo hbs hbc ιE μ ν hμu hνu hμic hνic hμc hνc hμν hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP μP νP hμP hνP hμicP hνicP hμcP hμνP rP hr hdistP ψf hψf hψjc hψhol hνcP hψdec ψ hψ hψrep em τ hem
  have hE1 := AutomorphicForm.inner_weylIntertwining_eq_sum_inner_mul_conj_inner_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν hμu hνu hμic hνic hμc hνc hμν hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP μP νP hμP hνP hμicP hνicP hμcP hμνP rP hr hdistP ψf hψf hψjc hψhol hψK hψsm hψKu hνcP hψdec ψ hψ hψrep em τ hem hψlev hψty

  set TP : (e : ιE) → Fin (nE e) → ℝ → ℂ := fun e j t =>
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hTP
  set Bm : (i : ιP) → Fin (nE (em i)) → Fin (nE (em (rP i))) → ℝ → ℂ := fun i j j' t =>
    ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) with hBm
  set Hh : (e : ιE) → Fin (nE e) → ℝ → ℂ := fun e j t => (∫ x : ℝ, h e j x * Complex.exp (((t : ℝ) : ℂ) * Complex.I * (x : ℂ))) with hHh

  have hoff : ∀ e : ιE, (∀ i : ιP, em i ≠ e) → ∀ (j : Fin (nE e)) (t : ℝ), TP e j t = 0 :=
    fun e he j t => hC.1 e he j t

  have hcoef : ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
      TP (em i) j (t + τ i) = (κ : ℂ) * (Hh (em i) j (t + τ i) +
        ∑ j' : Fin (nE (em (rP i))), Hh (em (rP i)) j' (-t + τ (rP i)) * conj (Bm i j j' t)) := by
    intro i j t
    have h1 : TP (em i) j (t + τ i) = _ := hC.2 i j t
    rw [h1]
    congr 1
    have hv : (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
          ∂(maximalCompactHaar K)) = Hh (em i) j (t + τ i) := hV1 i t j
    have hE := hE1 i j t
    have hv' : ∀ j' : Fin (nE (em (rP i))),
        (∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
          Hh (em (rP i)) j' (-t + τ (rP i)) := by
      intro j'
      have h := hV1 (rP i) (-t) j'
      have e0 : (((-t : ℝ) : ℂ)) * Complex.I = -((t : ℂ) * Complex.I) := by push_cast; ring
      rw [e0] at h
      exact h
    rw [hv, hE]
    congr 1
    exact Finset.sum_congr rfl fun j' _ => by rw [hv' j']

  have hsw : ∀ i : ιP, μ (em (rP i)) = ν (em i) * NumberField.TateGlobal.normPowChar K (-(τ i + τ (rP i))) ∧
      ν (em (rP i)) = μ (em i) * (NumberField.TateGlobal.normPowChar K (-(τ i + τ (rP i))))⁻¹ := by
    intro i
    obtain ⟨h1, h2⟩ := hem i
    obtain ⟨h3, h4⟩ := hem (rP i)
    obtain ⟨h5, h6⟩ := hr i
    constructor
    · refine MonoidHom.ext fun x => ?_
      have a2 := DFunLike.congr_fun h2 x
      have a3 := DFunLike.congr_fun h3 x
      have a5 := DFunLike.congr_fun h5 x
      rw [MonoidHom.mul_apply] at a2 a3 ⊢
      rw [MonoidHom.inv_apply] at a2
      rw [Ws48.FE2.normPowChar_neg, Ws48.FE2.normPowChar_add, MonoidHom.inv_apply, MonoidHom.mul_apply]
      have e3 : μ (em (rP i)) x = μP (rP i) x * (NumberField.TateGlobal.normPowChar K (τ (rP i)) x)⁻¹ := by
        rw [a3, mul_inv_cancel_right]
      rw [e3, a5, a2, mul_inv, mul_assoc]
    · refine MonoidHom.ext fun x => ?_
      have a1 := DFunLike.congr_fun h1 x
      have a4 := DFunLike.congr_fun h4 x
      have a6 := DFunLike.congr_fun h6 x
      rw [MonoidHom.mul_apply] at a1 a4 ⊢
      rw [MonoidHom.inv_apply] at a4 ⊢
      rw [Ws48.FE2.normPowChar_neg, MonoidHom.inv_apply, inv_inv, Ws48.FE2.normPowChar_add, MonoidHom.mul_apply]
      have e4 : ν (em (rP i)) x = νP (rP i) x * NumberField.TateGlobal.normPowChar K (τ (rP i)) x := by
        rw [a4, inv_mul_cancel_right]
      rw [e4, a6, a1, mul_assoc]
  have hsymi : ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
      F (em i) j (t + τ i) = ∑ j' : Fin (nE (em (rP i))), conj (Bm i j j' t) * F (em (rP i)) j' (-t + τ (rP i)) := by
    intro i j t
    have h := hFsym (em i) (em (rP i)) (-(τ i + τ (rP i))) (hsw i) j (t + τ i)
    have e1 : (-((t + τ i) + -(τ i + τ (rP i))) : ℝ) = -t + τ (rP i) := by ring
    have e2 : -((((t + τ i + -(τ i + τ (rP i)) : ℝ) : ℂ)) * Complex.I) = (((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I := by push_cast; ring
    rw [h]
    refine Finset.sum_congr rfl fun j' _ => ?_
    simp only [hBm, e2, e1]

  have hHh_cont : ∀ (e : ιE) (j : Fin (nE e)), Continuous (Hh e j) := by
    intro e j
    have hd := (MellinPaleyWiener.differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport (h e j) (hh1 e j).1 (hh1 e j).2).1
    exact hd.continuous.comp (Complex.continuous_ofReal.mul continuous_const)
  have hHh_L2 : ∀ (e : ιE) (j : Fin (nE e)), MemLp (Hh e j) 2 := by
    intro e j
    by_cases he : e ∈ F₀
    · have : Hh e j = fun t : ℝ => ∫ x : ℝ, hh e j x * Complex.exp (((t : ℝ) : ℂ) * Complex.I * (x : ℂ)) := by
        funext t; simp only [hHh, hhdef, he, if_true]
      rw [this]; exact hhL e j
    · have : Hh e j = fun _ : ℝ => (0 : ℂ) := by
        funext t; simp only [hHh, hhdef, he, if_false, Pi.zero_apply, zero_mul, integral_zero]
      rw [this]; exact MemLp.zero'
  have hφc : ∀ (e₀ : ιE) (j' : Fin (nE e₀)) (s : ℂ), Continuous fun k : ↥(adelicMaximalCompact K) => φE e₀ j' s (k : AdelicGL2 (𝓞 K) K) :=
    fun e₀ j' s => ((hφEjc e₀ j').comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val
  have hNEc : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)), Continuous fun p : ℝ × ↥(adelicMaximalCompact K) =>
      NE e₀ j₀ ((((p.1 : ℝ) : ℂ)) * Complex.I) (p.2 : AdelicGL2 (𝓞 K) K) := by
    intro e₀ j₀
    have hax : ∀ t : ℝ, ((t : ℂ) * Complex.I) ∈ OE e₀ j₀ := fun t => (hEE e₀ j₀).2.2.1 (by simp)
    refine ((hEE e₀ j₀).2.2.2.2.2.2.2.1).comp_continuous (f := fun p : ℝ × ↥(adelicMaximalCompact K) => ((((p.1 : ℝ) : ℂ)) * Complex.I, (p.2 : AdelicGL2 (𝓞 K) K))) ?_ (fun p => ⟨hax p.1, Set.mem_univ _⟩)
    exact Continuous.prodMk ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const) (continuous_subtype_val.comp continuous_snd)
  have hBm_cont : ∀ (i : ιP) (j : Fin (nE (em i))) (j' : Fin (nE (em (rP i)))), Continuous (Bm i j j') := by
    intro i j j'
    have hunc : Continuous (Function.uncurry fun (t : ℝ) (k' : ↥(adelicMaximalCompact K)) =>
        ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
          conj (φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))) := by
      refine Continuous.mul (continuous_const.mul ?_) (Complex.continuous_conj.comp ?_)
      · exact (hNEc (em i) j).comp (Continuous.prodMk (continuous_fst.add continuous_const) continuous_snd)
      · exact (hφEjc (em (rP i)) j').comp (Continuous.prodMk
          ((Complex.continuous_ofReal.comp (continuous_fst.neg.add continuous_const)).mul continuous_const)
          (continuous_subtype_val.comp continuous_snd))
    have := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar K) hunc isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hT_eq : ∀ (i : ιP) (j : Fin (nE (em i))) (s : ℝ), TP (em i) j s = (κ : ℂ) * (Hh (em i) j s +
      ∑ j' : Fin (nE (em (rP i))), Hh (em (rP i)) j' (-(s - τ i) + τ (rP i)) * conj (Bm i j j' (s - τ i))) := by
    intro i j s
    have := hcoef i j (s - τ i)
    rwa [sub_add_cancel] at this
  have hT_cont : ∀ (i : ιP) (j : Fin (nE (em i))), Continuous (TP (em i) j) := by
    intro i j
    have hfun : TP (em i) j = fun s => (κ : ℂ) * (Hh (em i) j s +
        ∑ j' : Fin (nE (em (rP i))), Hh (em (rP i)) j' (-(s - τ i) + τ (rP i)) * conj (Bm i j j' (s - τ i))) :=
      funext (hT_eq i j)
    rw [hfun]
    refine continuous_const.mul ((hHh_cont _ _).add (continuous_finsetSum _ fun j' _ => ?_))
    exact ((hHh_cont _ _).comp ((continuous_id.sub continuous_const).neg.add continuous_const)).mul
      (Complex.continuous_conj.comp ((hBm_cont i j j').comp (continuous_id.sub continuous_const)))
  set dd : (e : ιE) → Fin (nE e) → ℝ → ℂ := fun e j t => Hh e j t - (((2 * κ)⁻¹ : ℝ) : ℂ) * F e j t with hdd
  have hdd_L2 : ∀ (e : ιE) (j : Fin (nE e)), MemLp (dd e j) 2 := fun e j => (hHh_L2 e j).sub ((hF2 e j).const_mul _)
  have heq : ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
      TP (em i) j (t + τ i) - F (em i) j (t + τ i) =
        (κ : ℂ) * (dd (em i) j (t + τ i) + ∑ j' : Fin (nE (em (rP i))), conj (Bm i j j' t) * dd (em (rP i)) j' (-t + τ (rP i))) := by
    intro i j t
    rw [hcoef i j t]
    have hs := hsymi i j t
    have h2 : ∑ j' : Fin (nE (em (rP i))), conj (Bm i j j' t) * dd (em (rP i)) j' (-t + τ (rP i)) =
        ∑ j' : Fin (nE (em (rP i))), Hh (em (rP i)) j' (-t + τ (rP i)) * conj (Bm i j j' t) -
          (((2 * κ)⁻¹ : ℝ) : ℂ) * F (em i) j (t + τ i) := by
      rw [hs, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j' _ => by simp only [hdd]; ring
    rw [h2]
    simp only [hdd]
    have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    push_cast
    field_simp
    ring
  have hBAX := AutomorphicForm.sum_norm_sq_sum_conj_inner_weylIntertwining_mul_le_sum_norm_sq_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν hμu hνu hμic hνic hμc hνc hμν hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP μP νP hμP hνP hμicP hνicP hμcP hμνP rP hr hdistP ψf hψf hψjc hψhol hψK hψsm hψKu hνcP hψdec ψ hψ hψrep em τ hem hψlev hψty
  have hper : ∀ i : ιP, (∀ j : Fin (nE (em i)), MemLp (fun t => F (em i) j t - TP (em i) j t) 2) ∧
      ∫ t : ℝ, ∑ j : Fin (nE (em i)), ‖F (em i) j t - TP (em i) j t‖ ^ 2 ≤
        2 * κ ^ 2 * ((∑ j : Fin (nE (em i)), ∫ t : ℝ, ‖dd (em i) j t‖ ^ 2) +
          ∑ j' : Fin (nE (em (rP i))), ∫ t : ℝ, ‖dd (em (rP i)) j' t‖ ^ 2) :=
    fun i => MeasureTheory.memLp_two_and_integral_sum_norm_sq_sub_le_mul_add_of_eq_mul_add_sum_conj_mul_of_bessel κ (τ i) (τ (rP i)) (TP (em i)) (F (em i)) (dd (em i)) (dd (em (rP i))) (Bm i)
      (fun j => hdd_L2 _ j) (fun j' => hdd_L2 _ j')
      (fun j => (hT_cont i j).aestronglyMeasurable.sub (hF2 (em i) j).aestronglyMeasurable) (hBAX i) (heq i)

  set a' : ιE → ℝ := fun e => ∫ t : ℝ, ∑ j : Fin (nE e), ‖F e j t - TP e j t‖ ^ 2 with ha'
  have ha'_off : ∀ e : ιE, (∀ i : ιP, em i ≠ e) → a' e = a e := by
    intro e hne
    simp only [ha', ha, hoff e hne, sub_zero]
  have hsum' : Summable a' := by
    have hfin : Summable (fun e => a' e - a e) := by
      apply summable_of_finite_support
      refine (Set.finite_range em).subset ?_
      intro e he
      by_contra hne
      apply he
      have hne' : ∀ i : ιP, em i ≠ e := fun i hi => hne ⟨i, hi⟩
      show a' e - a e = 0
      rw [ha'_off e hne', sub_self]
    have := hFs.add hfin
    refine this.congr (fun e => ?_)
    show a e + (a' e - a e) = a' e
    ring
  refine ⟨ιP, instP, μP, νP, hμP, hνP, hμicP, hνicP, hμcP, hμνP, rP, hr, hdistP, ψf, hψf, hψjc, hψhol, hψK, hψsm, hψKu, hνcP, hψdec, ψ, hψ, hψrep, em, τ, hem, hψlev, hψty, pψ, hpψ, hpψc, hpψo, ?_, hsum', ?_⟩
  ·
    intro e j
    by_cases he : ∃ i : ιP, em i = e
    · obtain ⟨i, rfl⟩ := he
      exact (hper i).1 j
    · have hne : ∀ i : ιP, em i ≠ e := fun i hi => he ⟨i, hi⟩
      have hfun : (fun t : ℝ => F e j t - TP e j t) = F e j := by
        funext t; rw [hoff e hne j t, sub_zero]
      show MemLp (fun t : ℝ => F e j t - TP e j t) 2
      rw [hfun]; exact hF2 e j
  ·
    have hrr : Function.Involutive rP := by
      intro i
      by_contra hne
      obtain ⟨x, -, hx⟩ := hdistP (rP (rP i)) i hne
      rw [(hr (rP i)).1, (hr i).2, (hr (rP i)).2, (hr i).1] at hx
      exact hx.elim (fun h => h rfl) (fun h => h rfl)
    set c0 : ℝ := (2 * κ)⁻¹ with hc0
    set δ' : ℝ := ε ^ 2 / (16 * κ ^ 2 * (M₀ + 1)) with hδ'
    set D : ιE → ℝ := fun e => ∑ j : Fin (nE e), ∫ t : ℝ, ‖dd e j t‖ ^ 2 with hD
    set g : ιE → ℝ := fun e => if e ∈ F₀ then 0 else a e with hg
    have hg0 : ∀ e, 0 ≤ g e := fun e => by simp only [hg]; split_ifs; exact le_rfl; exact ha0 e
    have hga : ∀ e, g e ≤ a e := fun e => by simp only [hg]; split_ifs; exact ha0 e; exact le_rfl
    have hgs : Summable g := hFs.of_nonneg_of_le hg0 hga

    have hHh_off : ∀ e : ιE, e ∉ F₀ → ∀ (j : Fin (nE e)) (t : ℝ), Hh e j t = 0 := by
      intro e he j t; simp only [hHh, hhdef, he, if_false, Pi.zero_apply, zero_mul, integral_zero]

    have ha_zero : ∀ e : ιE, nE e = 0 → a e = 0 := by
      intro e he
      simp only [ha]
      have : ∀ t : ℝ, (∑ j : Fin (nE e), ‖F e j t‖ ^ 2) = 0 := fun t => by
        rw [Finset.sum_eq_zero]; intro j _; exact absurd j.2 (by omega)
      simp only [this, integral_zero]

    have hD_in : ∀ e ∈ F₀, D e ≤ (nE e : ℝ) * δ' := by
      intro e he
      have hj : ∀ j : Fin (nE e), ∫ t : ℝ, ‖dd e j t‖ ^ 2 ≤ δ' := by
        intro j
        have h1 := hhδ e j
        have heqf : (fun t : ℝ => ‖dd e j t‖ ^ 2) = fun t => ‖(((2 * κ)⁻¹ : ℝ) : ℂ) * F e j t -
            ∫ x : ℝ, hh e j x * Complex.exp (((t : ℝ) : ℂ) * Complex.I * (x : ℂ))‖ ^ 2 := by
          funext t; simp only [hdd, hHh, hhdef, he, if_true]; rw [norm_sub_rev]
        rw [heqf]; exact h1.le
      calc D e = ∑ j : Fin (nE e), ∫ t : ℝ, ‖dd e j t‖ ^ 2 := rfl
        _ ≤ ∑ j : Fin (nE e), δ' := Finset.sum_le_sum fun j _ => hj j
        _ = (nE e : ℝ) * δ' := by simp
    have hD_out : ∀ e : ιE, e ∉ F₀ → D e = c0 ^ 2 * a e := by
      intro e he
      have hint2 : ∀ j : Fin (nE e), Integrable (fun t : ℝ => ‖F e j t‖ ^ 2) :=
        fun j => (memLp_two_iff_integrable_sq_norm (hF2 e j).1).1 (hF2 e j)
      have hj : ∀ j : Fin (nE e), (fun t : ℝ => ‖dd e j t‖ ^ 2) = fun t => c0 ^ 2 * ‖F e j t‖ ^ 2 := by
        intro j; funext t
        simp only [hdd, hHh_off e he j t, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, hc0]
        rw [mul_pow, sq_abs]
      simp only [hD, hj, integral_const_mul, ← Finset.mul_sum, ha]
      rw [integral_finset_sum _ (fun j _ => hint2 j)]

    have hS : ∑ e ∈ Finset.univ.image em, a' e ≤ 4 * κ ^ 2 * ∑ e ∈ Finset.univ.image em, D e := by
      rw [Finset.sum_image (fun i _ i' _ h => hinj h), Finset.sum_image (fun i _ i' _ h => hinj h)]
      calc ∑ i : ιP, a' (em i) ≤ ∑ i : ιP, 2 * κ ^ 2 * (D (em i) + D (em (rP i))) :=
            Finset.sum_le_sum fun i _ => (hper i).2
        _ = 2 * κ ^ 2 * (∑ i : ιP, D (em i) + ∑ i : ιP, D (em (rP i))) := by
            rw [← Finset.sum_add_distrib, Finset.mul_sum]
        _ = 4 * κ ^ 2 * ∑ i : ιP, D (em i) := by
            have hperm : ∑ i : ιP, D (em (rP i)) = ∑ i : ιP, D (em i) :=
              Equiv.sum_comp (Function.Involutive.toPerm rP hrr) (fun i => D (em i))
            rw [hperm]; ring
    have hDsum : 4 * κ ^ 2 * ∑ e ∈ Finset.univ.image em, D e ≤ 4 * κ ^ 2 * (M₀ * δ') + ∑ e ∈ Finset.univ.image em, g e := by
      have hκ2 : 4 * κ ^ 2 * c0 ^ 2 = 1 := by rw [hc0]; field_simp; ring
      have hpt : ∀ e ∈ Finset.univ.image em, 4 * κ ^ 2 * D e ≤ 4 * κ ^ 2 * ((if e ∈ F₀ then (nE e : ℝ) else 0) * δ') + g e := by
        intro e _
        by_cases he : e ∈ F₀
        · simp only [he, if_true, hg]
          have := hD_in e he
          nlinarith [sq_nonneg κ]
        · simp only [he, if_false, hg, zero_mul, mul_zero, zero_add]
          rw [hD_out e he, ← mul_assoc, hκ2, one_mul]
      calc 4 * κ ^ 2 * ∑ e ∈ Finset.univ.image em, D e = ∑ e ∈ Finset.univ.image em, 4 * κ ^ 2 * D e := Finset.mul_sum _ _ _
        _ ≤ ∑ e ∈ Finset.univ.image em, (4 * κ ^ 2 * ((if e ∈ F₀ then (nE e : ℝ) else 0) * δ') + g e) := Finset.sum_le_sum hpt
        _ = 4 * κ ^ 2 * ((∑ e ∈ Finset.univ.image em, (if e ∈ F₀ then (nE e : ℝ) else 0)) * δ') + ∑ e ∈ Finset.univ.image em, g e := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_mul]
        _ ≤ 4 * κ ^ 2 * (M₀ * δ') + ∑ e ∈ Finset.univ.image em, g e := by
            gcongr
            · calc ∑ e ∈ Finset.univ.image em, (if e ∈ F₀ then (nE e : ℝ) else 0)
                  = ∑ e ∈ (Finset.univ.image em).filter (· ∈ F₀), (nE e : ℝ) := by rw [Finset.sum_filter]
                _ ≤ ∑ e ∈ F₀, (nE e : ℝ) := by
                    apply Finset.sum_le_sum_of_subset_of_nonneg
                    · intro e he; simp only [Finset.mem_filter] at he; exact he.2
                    · intro e _ _; positivity
                _ = (M₀ : ℝ) := by simp [hM₀]

    have hT : ∑' e : {e : ιE // e ∉ Finset.univ.image em}, a' e ≤ ∑' e : {e : ιE // e ∉ Finset.univ.image em}, g e := by
      refine Summable.tsum_le_tsum (fun e => ?_) (hsum'.subtype _) (hgs.subtype _)
      have hne : ∀ i : ιP, em i ≠ e := fun i hi => e.2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
      rw [ha'_off e hne]
      simp only [hg]
      split_ifs with heF
      · have : nE e = 0 := by
          by_contra h0
          obtain ⟨i, hi⟩ := hcov e heF (Nat.pos_of_ne_zero h0)
          exact hne i hi
        rw [ha_zero e this]
      · exact le_rfl

    have htail : ∑' e, g e < ε ^ 2 / 8 := by
      have h1 : (∑' e : {e : ιE // e ∉ F₀}, a e) = ∑' e, g e := by
        rw [show (∑' e : {e : ιE // e ∉ F₀}, a e) = ∑' e : ↥({e : ιE | e ∉ F₀} : Set ιE), a e from rfl, tsum_subtype]
        congr 1; funext e
        by_cases he : e ∈ F₀
        · simp [hg, he]
        · simp [hg, he]
      rw [← h1]; exact hF₀

    rw [← hsum'.sum_add_tsum_compl (s := Finset.univ.image em)]
    have hgsplit := hgs.sum_add_tsum_compl (s := Finset.univ.image em)
    have hM : 4 * κ ^ 2 * (M₀ * δ') ≤ ε ^ 2 / 4 := by
      have hκ0 : κ ≠ 0 := hκ.ne'
      have hM1 : (M₀ : ℝ) + 1 ≠ 0 := by positivity
      have h1 : 4 * κ ^ 2 * ((M₀ : ℝ) * δ') = ε ^ 2 / 4 * ((M₀ : ℝ) / ((M₀ : ℝ) + 1)) := by
        rw [hδ']; field_simp; ring
      have h2 : (M₀ : ℝ) / ((M₀ : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      rw [h1]
      calc ε ^ 2 / 4 * ((M₀ : ℝ) / ((M₀ : ℝ) + 1)) ≤ ε ^ 2 / 4 * 1 := by gcongr
        _ = ε ^ 2 / 4 := mul_one _
    calc ∑ e ∈ Finset.univ.image em, a' e + ∑' e : {e : ιE // e ∉ Finset.univ.image em}, a' e
        ≤ (4 * κ ^ 2 * (M₀ * δ') + ∑ e ∈ Finset.univ.image em, g e) + ∑' e : {e : ιE // e ∉ Finset.univ.image em}, g e :=
          add_le_add (hS.trans hDsum) hT
      _ = 4 * κ ^ 2 * (M₀ * δ') + ∑' e, g e := by
          have hg' : (∑ e ∈ Finset.univ.image em, g e) + ∑' e : {e : ιE // e ∉ Finset.univ.image em}, g e = ∑' e, g e := hgsplit
          rw [add_assoc, hg']
      _ ≤ ε ^ 2 / 4 + ε ^ 2 / 8 := add_le_add hM htail.le
      _ ≤ ε ^ 2 := by nlinarith [sq_nonneg ε]

end S_AutomorphicForm_exists_matched_paleyWiener_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le_of_symmetric
end P2MW
export P2MW.S_AutomorphicForm_exists_matched_paleyWiener_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le_of_symmetric (solution)
