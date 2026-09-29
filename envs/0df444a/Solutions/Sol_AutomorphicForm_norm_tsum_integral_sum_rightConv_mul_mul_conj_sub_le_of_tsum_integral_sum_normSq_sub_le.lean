-- Prove2me | solution 1 for AutomorphicForm.norm_tsum_integral_sum_rightConv_mul_mul_conj_sub_le_of_tsum_integral_sum_normSq_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e2716a67-ddae-5de5-a938-5c4c2ede4f10

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
import Theorems.Thm_AutomorphicForm_continuous_integral_rightConv_axis_mul_conj_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_norm_tsum_integral_sum_rightConv_mul_mul_conj_sub_le_of_tsum_integral_sum_normSq_sub_le
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace Ws1
namespace RHSStab

variable {ιE : Type} {n : ιE → ℕ}

theorem q_nonneg (U : ∀ e : ιE, Fin (n e) → ℝ → ℂ) (e : ιE) (t : ℝ) : 0 ≤ (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) :=
  Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) 2

theorem good_facts (U : ∀ e : ιE, Fin (n e) → ℝ → ℂ) (hU : ((∀ (e : ιE) (j : Fin (n e)), MemLp (U e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))))) (e : ιE) :
    Integrable (fun t : ℝ => (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) ∧
      MemLp (fun t : ℝ => Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) 2 ∧ 0 ≤ (∫ t : ℝ, (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) := by
  have hI : Integrable (fun t : ℝ => (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) :=
    integrable_finset_sum _ fun j _ => (memLp_two_iff_integrable_sq_norm (hU.1 e j).1).1 (hU.1 e j)
  refine ⟨hI, ?_, integral_nonneg fun t => q_nonneg U e t⟩
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hI.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine hI.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (q_nonneg U e t)]

theorem pair_cs (U V : ∀ e : ιE, Fin (n e) → ℝ → ℂ) (hU : ((∀ (e : ιE) (j : Fin (n e)), MemLp (U e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))))) (hV : ((∀ (e : ιE) (j : Fin (n e)), MemLp (V e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))))) :
    (∀ e : ιE, Integrable (fun t : ℝ => Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ)))) ∧
    (∀ e : ιE, ∫ t : ℝ, Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ)) ≤ Real.sqrt (∫ t : ℝ, (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) * Real.sqrt (∫ t : ℝ, (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ)))) ∧
    Summable (fun e : ιE => ∫ t : ℝ, Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))) ∧
    ∑' e : ιE, ∫ t : ℝ, Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ)) ≤ Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))) := by
  have hI : ∀ e : ιE, Integrable (fun t : ℝ => Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))) := fun e =>
    (good_facts U hU e).2.1.integrable_mul (good_facts V hV e).2.1
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hsqU : ∀ (e : ιE) (t : ℝ), Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) ^ 2 = (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) := fun e t => Real.sq_sqrt (q_nonneg U e t)
  have hsqV : ∀ (e : ιE) (t : ℝ), Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ)) ^ 2 = (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ)) := fun e t => Real.sq_sqrt (q_nonneg V e t)
  have hcs : ∀ e : ιE, ∫ t : ℝ, Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ)) ≤ Real.sqrt (∫ t : ℝ, (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) * Real.sqrt (∫ t : ℝ, (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))) := by
    intro e
    have hf : MemLp (fun t : ℝ => Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) (ENNReal.ofReal 2) := by rw [h2]; exact (good_facts U hU e).2.1
    have hg : MemLp (fun t : ℝ => Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))) (ENNReal.ofReal 2) := by rw [h2]; exact (good_facts V hV e).2.1
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg _) (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg _) hf hg
    simp only [Real.rpow_two, hsqU, hsqV] at h
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
    exact h

  have hfn : ∀ e : ιE, 0 ≤ Real.sqrt (∫ t : ℝ, (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) := fun e => Real.sqrt_nonneg _
  have hgn : ∀ e : ιE, 0 ≤ Real.sqrt (∫ t : ℝ, (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))) := fun e => Real.sqrt_nonneg _
  have hfs : Summable (fun e : ιE => Real.sqrt (∫ t : ℝ, (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) ^ (2 : ℝ)) := by
    simp only [Real.rpow_two, Real.sq_sqrt (good_facts U hU _).2.2]; exact hU.2
  have hgs : Summable (fun e : ιE => Real.sqrt (∫ t : ℝ, (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))) ^ (2 : ℝ)) := by
    simp only [Real.rpow_two, Real.sq_sqrt (good_facts V hV _).2.2]; exact hV.2
  have hS := Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two hfn hgn hfs hgs
  have hT := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two hfn hgn hfs hgs
  simp only [Real.rpow_two, Real.sq_sqrt (good_facts U hU _).2.2, Real.sq_sqrt (good_facts V hV _).2.2] at hT
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hT
  have hcn : ∀ e : ιE, 0 ≤ ∫ t : ℝ, Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ)) := fun e =>
    integral_nonneg fun t => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcS : Summable (fun e : ιE => ∫ t : ℝ, Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))) := Summable.of_nonneg_of_le hcn hcs hS
  exact ⟨hI, hcs, hcS, (hcS.tsum_le_tsum hcs hS).trans hT⟩

theorem pair_bound (a : ∀ e : ιE, ℝ → Fin (n e) → Fin (n e) → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (ha_meas : ∀ (e : ιE) (i j : Fin (n e)), AEStronglyMeasurable (fun t : ℝ => a e t i j) volume)
    (ha_bd : ∀ (e : ιE) (t : ℝ) (u v : Fin (n e) → ℂ),
      ‖∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (v j * conj (u i))‖ ≤
        L * Real.sqrt (∑ i : Fin (n e), ‖u i‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖v j‖ ^ (2 : ℕ)))
    (U V : ∀ e : ιE, Fin (n e) → ℝ → ℂ) (hU : ((∀ (e : ιE) (j : Fin (n e)), MemLp (U e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))))) (hV : ((∀ (e : ιE) (j : Fin (n e)), MemLp (V e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))))) :
    (∀ e : ιE, Integrable (fun t : ℝ => (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (V e j t * conj (U e i t))))) ∧
    Summable (fun e : ιE => ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (V e j t * conj (U e i t)))) ∧
    ‖∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (V e j t * conj (U e i t)))‖ ≤ L * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))) := by
  obtain ⟨hI, -, hcS, hT⟩ := pair_cs U V hU hV
  have hpt : ∀ (e : ιE) (t : ℝ), ‖(∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (V e j t * conj (U e i t)))‖ ≤ L * (Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))) := fun e t => by
    rw [← mul_assoc]; exact ha_bd e t (fun i => U e i t) (fun j => V e j t)
  have hmeas : ∀ e : ιE, AEStronglyMeasurable (fun t : ℝ => (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (V e j t * conj (U e i t)))) volume := fun e =>
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      (ha_meas e i j).mul ((hV.1 e j).1.mul (Complex.continuous_conj.comp_aestronglyMeasurable (hU.1 e i).1))
  have hBI : ∀ e : ιE, Integrable (fun t : ℝ => (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (V e j t * conj (U e i t)))) := fun e =>
    Integrable.mono' ((hI e).const_mul L) (hmeas e) (Filter.Eventually.of_forall (hpt e))
  have hBn : ∀ e : ιE, ‖∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (V e j t * conj (U e i t)))‖ ≤ L * ∫ t : ℝ, Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ)) := fun e => by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    exact integral_mono (hBI e).norm ((hI e).const_mul L) (hpt e)
  have hBS : Summable (fun e : ιE => ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (V e j t * conj (U e i t)))) := Summable.of_norm_bounded (hcS.mul_left L) hBn
  refine ⟨hBI, hBS, ?_⟩
  have hnS : Summable (fun e : ιE => ‖∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (V e j t * conj (U e i t)))‖) :=
    Summable.of_nonneg_of_le (fun e => norm_nonneg _) hBn (hcS.mul_left L)
  calc ‖∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (V e j t * conj (U e i t)))‖ ≤ ∑' e : ιE, ‖∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (V e j t * conj (U e i t)))‖ := norm_tsum_le_tsum_norm hnS
    _ ≤ ∑' e : ιE, L * ∫ t : ℝ, Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ)) := hnS.tsum_le_tsum hBn (hcS.mul_left L)
    _ = L * ∑' e : ιE, ∫ t : ℝ, Real.sqrt (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ)) := tsum_mul_left
    _ ≤ L * (Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ)))) := mul_le_mul_of_nonneg_left hT hL
    _ = L * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖U e j t‖ ^ (2 : ℕ))) * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖V e j t‖ ^ (2 : ℕ))) := by ring

theorem good_of_sub (X Y : ∀ e : ιE, Fin (n e) → ℝ → ℂ) (hY : ((∀ (e : ιE) (j : Fin (n e)), MemLp (Y e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖Y e j t‖ ^ (2 : ℕ)))))
    (hD : (∀ (e : ιE) (j : Fin (n e)), MemLp (fun t : ℝ => X e j t - Y e j t) 2) ∧
      Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖X e j t - Y e j t‖ ^ (2 : ℕ)))) : ((∀ (e : ιE) (j : Fin (n e)), MemLp (X e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖X e j t‖ ^ (2 : ℕ)))) := by
  have hX1 : ∀ (e : ιE) (j : Fin (n e)), MemLp (X e j) 2 := by
    intro e j
    have : X e j = fun t => Y e j t + (X e j t - Y e j t) := funext fun t => by ring
    rw [this]
    exact (hY.1 e j).add (hD.1 e j)
  refine ⟨hX1, ?_⟩
  have hIX : ∀ e : ιE, Integrable (fun t : ℝ => (∑ j : Fin (n e), ‖X e j t‖ ^ (2 : ℕ))) := fun e =>
    integrable_finset_sum _ fun j _ => (memLp_two_iff_integrable_sq_norm (hX1 e j).1).1 (hX1 e j)
  have hIY : ∀ e : ιE, Integrable (fun t : ℝ => (∑ j : Fin (n e), ‖Y e j t‖ ^ (2 : ℕ))) := fun e =>
    integrable_finset_sum _ fun j _ => (memLp_two_iff_integrable_sq_norm (hY.1 e j).1).1 (hY.1 e j)
  have hID : ∀ e : ιE, Integrable (fun t : ℝ => (∑ j : Fin (n e), ‖X e j t - Y e j t‖ ^ (2 : ℕ))) := fun e =>
    integrable_finset_sum _ fun j _ => (memLp_two_iff_integrable_sq_norm (hD.1 e j).1).1 (hD.1 e j)
  have hpt : ∀ (e : ιE) (t : ℝ), (∑ j : Fin (n e), ‖X e j t‖ ^ (2 : ℕ)) ≤ 2 * (∑ j : Fin (n e), ‖Y e j t‖ ^ (2 : ℕ)) + 2 * (∑ j : Fin (n e), ‖X e j t - Y e j t‖ ^ (2 : ℕ)) := by
    intro e t
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : ‖X e j t‖ ≤ ‖Y e j t‖ + ‖X e j t - Y e j t‖ := by
      have := norm_add_le (Y e j t) (X e j t - Y e j t)
      rwa [add_sub_cancel] at this
    calc ‖X e j t‖ ^ (2 : ℕ) ≤ (‖Y e j t‖ + ‖X e j t - Y e j t‖) ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ 2 * ‖Y e j t‖ ^ (2 : ℕ) + 2 * ‖X e j t - Y e j t‖ ^ (2 : ℕ) := by
          nlinarith [sq_nonneg (‖Y e j t‖ - ‖X e j t - Y e j t‖)]
  have hle : ∀ e : ιE, (∫ t : ℝ, (∑ j : Fin (n e), ‖X e j t‖ ^ (2 : ℕ))) ≤ 2 * (∫ t : ℝ, (∑ j : Fin (n e), ‖Y e j t‖ ^ (2 : ℕ))) + 2 * (∫ t : ℝ, (∑ j : Fin (n e), ‖X e j t - Y e j t‖ ^ (2 : ℕ))) := by
    intro e
    have hI2 : Integrable (fun t : ℝ => 2 * (∑ j : Fin (n e), ‖Y e j t‖ ^ (2 : ℕ)) + 2 * (∑ j : Fin (n e), ‖X e j t - Y e j t‖ ^ (2 : ℕ))) :=
      ((hIY e).const_mul 2).add ((hID e).const_mul 2)
    have h := integral_mono (hIX e) hI2 (hpt e)
    rw [integral_add ((hIY e).const_mul 2) ((hID e).const_mul 2), integral_const_mul, integral_const_mul] at h
    exact h
  exact Summable.of_nonneg_of_le (fun e => integral_nonneg fun t => q_nonneg X e t) hle
    ((hY.2.mul_left 2).add (hD.2.mul_left 2))

theorem abstract_stability (a : ∀ e : ιE, ℝ → Fin (n e) → Fin (n e) → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (ha_meas : ∀ (e : ιE) (i j : Fin (n e)), AEStronglyMeasurable (fun t : ℝ => a e t i j) volume)
    (ha_bd : ∀ (e : ιE) (t : ℝ) (u v : Fin (n e) → ℂ),
      ‖∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (v j * conj (u i))‖ ≤
        L * Real.sqrt (∑ i : Fin (n e), ‖u i‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin (n e), ‖v j‖ ^ (2 : ℕ)))
    (ε : ℝ) (hε : 0 < ε) (X₁ X₂ Y₁ Y₂ : ∀ e : ιE, Fin (n e) → ℝ → ℂ)
    (hY₁ : ((∀ (e : ιE) (j : Fin (n e)), MemLp (Y₁ e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖Y₁ e j t‖ ^ (2 : ℕ))))) (hY₂ : ((∀ (e : ιE) (j : Fin (n e)), MemLp (Y₂ e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖Y₂ e j t‖ ^ (2 : ℕ)))))
    (hD₁ : (∀ (e : ιE) (j : Fin (n e)), MemLp (fun t : ℝ => X₁ e j t - Y₁ e j t) 2) ∧
      Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖X₁ e j t - Y₁ e j t‖ ^ (2 : ℕ))) ∧
      ∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖X₁ e j t - Y₁ e j t‖ ^ (2 : ℕ)) ≤ ε ^ (2 : ℕ))
    (hD₂ : (∀ (e : ιE) (j : Fin (n e)), MemLp (fun t : ℝ => X₂ e j t - Y₂ e j t) 2) ∧
      Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖X₂ e j t - Y₂ e j t‖ ^ (2 : ℕ))) ∧
      ∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖X₂ e j t - Y₂ e j t‖ ^ (2 : ℕ)) ≤ ε ^ (2 : ℕ)) :
    (∀ e : ιE, Integrable (fun t : ℝ => (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (X₁ e i t))))) ∧
    Summable (fun e : ιE => ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (X₁ e i t)))) ∧
    (∀ e : ιE, Integrable (fun t : ℝ => (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (Y₂ e j t * conj (Y₁ e i t))))) ∧
    Summable (fun e : ιE => ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (Y₂ e j t * conj (Y₁ e i t)))) ∧
    ‖(∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (X₁ e i t)))) - (∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (Y₂ e j t * conj (Y₁ e i t))))‖ ≤
      L * ε * (Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖X₁ e j t‖ ^ (2 : ℕ))) + Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖X₂ e j t‖ ^ (2 : ℕ))) + ε) := by

  set D₁ : ∀ e : ιE, Fin (n e) → ℝ → ℂ := fun e i t => X₁ e i t - Y₁ e i t with hD₁def
  set D₂ : ∀ e : ιE, Fin (n e) → ℝ → ℂ := fun e i t => X₂ e i t - Y₂ e i t with hD₂def
  have gD₁ : ((∀ (e : ιE) (j : Fin (n e)), MemLp (D₁ e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖D₁ e j t‖ ^ (2 : ℕ)))) := ⟨hD₁.1, hD₁.2.1⟩
  have gD₂ : ((∀ (e : ιE) (j : Fin (n e)), MemLp (D₂ e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖D₂ e j t‖ ^ (2 : ℕ)))) := ⟨hD₂.1, hD₂.2.1⟩
  have gX₁ : ((∀ (e : ιE) (j : Fin (n e)), MemLp (X₁ e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖X₁ e j t‖ ^ (2 : ℕ)))) := good_of_sub X₁ Y₁ hY₁ ⟨hD₁.1, hD₁.2.1⟩
  have gX₂ : ((∀ (e : ιE) (j : Fin (n e)), MemLp (X₂ e j) 2) ∧ Summable (fun e : ιE => ∫ t : ℝ, (∑ j : Fin (n e), ‖X₂ e j t‖ ^ (2 : ℕ)))) := good_of_sub X₂ Y₂ hY₂ ⟨hD₂.1, hD₂.2.1⟩
  obtain ⟨iXX, sXX, -⟩ := pair_bound a L hL ha_meas ha_bd X₁ X₂ gX₁ gX₂
  obtain ⟨iYY, sYY, -⟩ := pair_bound a L hL ha_meas ha_bd Y₁ Y₂ hY₁ hY₂
  obtain ⟨iDX, sDX, bDX⟩ := pair_bound a L hL ha_meas ha_bd D₁ X₂ gD₁ gX₂
  obtain ⟨iXD, sXD, bXD⟩ := pair_bound a L hL ha_meas ha_bd X₁ D₂ gX₁ gD₂
  obtain ⟨iDD, sDD, bDD⟩ := pair_bound a L hL ha_meas ha_bd D₁ D₂ gD₁ gD₂
  refine ⟨iXX, sXX, iYY, sYY, ?_⟩

  have halg : ∀ (e : ιE) (t : ℝ), (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (X₁ e i t))) - (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (Y₂ e j t * conj (Y₁ e i t))) =
      (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (D₁ e i t))) + (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (X₁ e i t))) - (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (D₁ e i t))) := by
    intro e t
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hD₁def, hD₂def, map_sub]
    ring
  have hint : ∀ e : ιE, (∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (X₁ e i t)))) - (∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (Y₂ e j t * conj (Y₁ e i t)))) =
      (∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (D₁ e i t)))) + (∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (X₁ e i t)))) - (∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (D₁ e i t)))) := by
    intro e
    have hadd : Integrable (fun t : ℝ => (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (D₁ e i t))) + (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (X₁ e i t)))) := (iDX e).add (iXD e)
    calc (∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (X₁ e i t)))) - (∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (Y₂ e j t * conj (Y₁ e i t))))
        = ∫ t : ℝ, ((∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (X₁ e i t))) - (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (Y₂ e j t * conj (Y₁ e i t)))) := (integral_sub (iXX e) (iYY e)).symm
      _ = ∫ t : ℝ, ((∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (D₁ e i t))) + (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (X₁ e i t))) - (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (D₁ e i t)))) :=
          integral_congr_ae (Filter.Eventually.of_forall (halg e))
      _ = (∫ t : ℝ, ((∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (D₁ e i t))) + (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (X₁ e i t))))) - (∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (D₁ e i t)))) := integral_sub hadd (iDD e)
      _ = _ := by rw [integral_add (iDX e) (iXD e)]
  have htsum : (∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (X₁ e i t)))) - (∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (Y₂ e j t * conj (Y₁ e i t)))) =
      (∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (D₁ e i t)))) + (∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (X₁ e i t)))) -
        (∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (D₁ e i t)))) := by
    rw [← sXX.tsum_sub sYY, ← sDX.tsum_add sXD, ← (sDX.add sXD).tsum_sub sDD]
    exact tsum_congr hint

  have hND₁ : Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖D₁ e j t‖ ^ (2 : ℕ))) ≤ ε := by
    calc Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖D₁ e j t‖ ^ (2 : ℕ))) ≤ Real.sqrt (ε ^ (2 : ℕ)) := Real.sqrt_le_sqrt hD₁.2.2
      _ = ε := Real.sqrt_sq hε.le
  have hND₂ : Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖D₂ e j t‖ ^ (2 : ℕ))) ≤ ε := by
    calc Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖D₂ e j t‖ ^ (2 : ℕ))) ≤ Real.sqrt (ε ^ (2 : ℕ)) := Real.sqrt_le_sqrt hD₂.2.2
      _ = ε := Real.sqrt_sq hε.le
  have hNX₁ : 0 ≤ Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖X₁ e j t‖ ^ (2 : ℕ))) := Real.sqrt_nonneg _
  have hNX₂ : 0 ≤ Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖X₂ e j t‖ ^ (2 : ℕ))) := Real.sqrt_nonneg _
  have hND₁' : 0 ≤ Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖D₁ e j t‖ ^ (2 : ℕ))) := Real.sqrt_nonneg _
  have hND₂' : 0 ≤ Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖D₂ e j t‖ ^ (2 : ℕ))) := Real.sqrt_nonneg _
  rw [htsum]
  calc ‖(∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (D₁ e i t)))) + (∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (X₁ e i t)))) -
        (∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (D₁ e i t))))‖
      ≤ ‖∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (X₂ e j t * conj (D₁ e i t)))‖ + ‖∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (X₁ e i t)))‖ +
        ‖∑' e : ιE, ∫ t : ℝ, (∑ i : Fin (n e), ∑ j : Fin (n e), a e t i j * (D₂ e j t * conj (D₁ e i t)))‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ ≤ L * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖D₁ e j t‖ ^ (2 : ℕ))) * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖X₂ e j t‖ ^ (2 : ℕ))) + L * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖X₁ e j t‖ ^ (2 : ℕ))) * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖D₂ e j t‖ ^ (2 : ℕ))) + L * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖D₁ e j t‖ ^ (2 : ℕ))) * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖D₂ e j t‖ ^ (2 : ℕ))) :=
        add_le_add (add_le_add bDX bXD) bDD
    _ ≤ L * ε * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖X₂ e j t‖ ^ (2 : ℕ))) + L * Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖X₁ e j t‖ ^ (2 : ℕ))) * ε + L * ε * ε := by
        gcongr
    _ = L * ε * (Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖X₁ e j t‖ ^ (2 : ℕ))) + Real.sqrt (∑' e : ιE, ∫ t : ℝ, (∑ j : Fin (n e), ‖X₂ e j t‖ ^ (2 : ℕ))) + ε) := by ring

end Ws1.RHSStab

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace MatrixNormAx

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

scoped instance : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

theorem mul_conj_eq_ofReal (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem integrable_restrict {F : AdelicGL2 (𝓞 K) K → ℂ} (hF : Continuous F) :
    Integrable (fun k : adelicMaximalCompact K => F (k : AdelicGL2 (𝓞 K) K)) (maximalCompactHaar K) :=
  (hF.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem memLp_two_restrict {F : AdelicGL2 (𝓞 K) K → ℝ} (hF : Continuous F) :
    MemLp (fun k : adelicMaximalCompact K => F (k : AdelicGL2 (𝓞 K) K)) (ENNReal.ofReal 2) (maximalCompactHaar K) :=
  (hF.comp continuous_subtype_val).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem norm_integral_mul_conj_le {a b : AdelicGL2 (𝓞 K) K → ℂ} (ha : Continuous a) (hb : Continuous b) :
    ‖∫ k, a (k : AdelicGL2 (𝓞 K) K) * conj (b (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖ ≤
      (∫ k, ‖a (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K)) ^ (1 / 2 : ℝ) *
        (∫ k, ‖b (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K)) ^ (1 / 2 : ℝ) := by
  have h1 : ‖∫ k, a (k : AdelicGL2 (𝓞 K) K) * conj (b (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖ ≤
      ∫ k, ‖a (k : AdelicGL2 (𝓞 K) K)‖ * ‖b (k : AdelicGL2 (𝓞 K) K)‖ ∂(maximalCompactHaar K) := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext k; rw [norm_mul, Complex.norm_conj]
  have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := maximalCompactHaar K) Real.HolderConjugate.two_two
    (f := fun k : adelicMaximalCompact K => ‖a (k : AdelicGL2 (𝓞 K) K)‖)
    (g := fun k : adelicMaximalCompact K => ‖b (k : AdelicGL2 (𝓞 K) K)‖)
    (Filter.Eventually.of_forall fun _ => norm_nonneg _) (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (memLp_two_restrict K (F := fun g => ‖a g‖) ha.norm) (memLp_two_restrict K (F := fun g => ‖b g‖) hb.norm)
  simp only [Real.rpow_two] at h2
  exact h1.trans h2

theorem norm_sq_borel_mul (αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 K) K μ) (hν : IsUnitaryChar (𝓞 K) K ν)
    (t : ℝ) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ)
    (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    ((‖φ (b * g)‖ ^ 2 : ℝ) : ℂ) =
      ((((αm (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ) /
          ((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ) : ℝ) : ℂ) *
        ((‖φ g‖ ^ 2 : ℝ) : ℂ) := by
  set s : ℂ := (t : ℂ) * Complex.I with hs
  have hsre : s.re = 0 := by simp [hs]
  set x₁ := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K)) with hx₁
  set x₂ := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K)) with hx₂
  have hA : 0 < ((αm x₁ : ℝˣ) : ℝ) := hαm x₁
  have hD : 0 < ((αm x₂ : ℝˣ) : ℝ) := hαm x₂
  have h1 : ‖((etaFst μ αm hαm s x₁ : ℂˣ) : ℂ)‖ = ((αm x₁ : ℝˣ) : ℝ) ^ (1 / 2 : ℝ) := by
    rw [norm_etaFst_apply_of_unitary hμ, hsre, zero_add]
  have h2 : ‖((etaSnd ν αm hαm s x₂ : ℂˣ) : ℂ)‖ = ((αm x₂ : ℝˣ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [etaSnd_apply, Units.val_mul, norm_mul, hν x₂, one_mul, norm_cpowChar_apply]
    congr 1
    simp [hs]
  have hφb : φ (b * g) = ((etaFst μ αm hαm s x₁ : ℂˣ) : ℂ) * ((etaSnd ν αm hαm s x₂ : ℂˣ) : ℂ) * φ g :=
    hφ b hb g
  have hnorm : ‖φ (b * g)‖ ^ 2 =
      (((αm x₁ : ℝˣ) : ℝ) / ((αm x₂ : ℝˣ) : ℝ)) * ‖φ g‖ ^ 2 := by
    rw [hφb, norm_mul, norm_mul, h1, h2]
    have hsq1 : (((αm x₁ : ℝˣ) : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = ((αm x₁ : ℝˣ) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]; norm_num
    have hsq2 : (((αm x₂ : ℝˣ) : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = ((αm x₂ : ℝˣ) : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le, ← Real.rpow_neg_one]; norm_num
    calc (((αm x₁ : ℝˣ) : ℝ) ^ (1 / 2 : ℝ) * ((αm x₂ : ℝˣ) : ℝ) ^ (-(1 / 2 : ℝ)) * ‖φ g‖) ^ 2
        = (((αm x₁ : ℝˣ) : ℝ) ^ (1 / 2 : ℝ)) ^ 2 * (((αm x₂ : ℝˣ) : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * ‖φ g‖ ^ 2 := by ring
      _ = ((αm x₁ : ℝˣ) : ℝ) * ((αm x₂ : ℝˣ) : ℝ)⁻¹ * ‖φ g‖ ^ 2 := by rw [hsq1, hsq2]
      _ = (((αm x₁ : ℝˣ) : ℝ) / ((αm x₂ : ℝˣ) : ℝ)) * ‖φ g‖ ^ 2 := by rw [div_eq_mul_inv]
  rw [hnorm]; push_cast; ring

end MatrixNormAx
p2m_reactivate "P2MW.S_AutomorphicForm_norm_tsum_integral_sum_rightConv_mul_mul_conj_sub_le_of_tsum_integral_sum_normSq_sub_le.MatrixNormAx"

open AutomorphicForm in

theorem MatrixNormAx.pairing_bound
    (K : Type) [Field K] [NumberField K]
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (t : ℝ) (φ ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hφc : Continuous φ) (_hψc : Continuous ψ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I))
        (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ)
      (_hψ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I))
        (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) ψ),
    ‖∫ k, rightConv K φ f (k : AdelicGL2 (𝓞 K) K) * conj (ψ (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖ ≤
      (∫ g, ‖f g‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
        Real.sqrt (∫ k, ‖φ (k : AdelicGL2 (𝓞 K) K)‖ ^ (2 : ℕ) ∂(maximalCompactHaar K)) *
        Real.sqrt (∫ k, ‖ψ (k : AdelicGL2 (𝓞 K) K)‖ ^ (2 : ℕ) ∂(maximalCompactHaar K)) := by
  intro αm hαm μ ν hμ hν t φ ψ hφc hψc hφ hψ

  set Nφ : ℝ := ∫ k, ‖φ (k : AdelicGL2 (𝓞 K) K)‖ ^ (2 : ℕ) ∂(maximalCompactHaar K) with hNφ
  set Nψ : ℝ := ∫ k, ‖ψ (k : AdelicGL2 (𝓞 K) K)‖ ^ (2 : ℕ) ∂(maximalCompactHaar K) with hNψ
  have hNφ0 : 0 ≤ Nφ := integral_nonneg fun _ => by positivity
  have hNψ0 : 0 ≤ Nψ := integral_nonneg fun _ => by positivity
  have hφny : ∀ y : AdelicGL2 (𝓞 K) K,
      ∫ k, ‖φ ((k : AdelicGL2 (𝓞 K) K) * y)‖ ^ (2 : ℕ) ∂(maximalCompactHaar K) = Nφ := by
    intro y
    have hinv := AutomorphicForm.integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul K
      (fun g => ((‖φ g‖ ^ 2 : ℝ) : ℂ)) (Complex.continuous_ofReal.comp (hφc.norm.pow 2))
      (fun b hb g => MatrixNormAx.norm_sq_borel_mul K αm hαm hμ hν t hφ b hb g) y
    have h' : ∫ k, ((‖φ ((k : AdelicGL2 (𝓞 K) K) * y)‖ ^ 2 : ℝ) : ℂ) ∂(maximalCompactHaar K) =
        ((Nφ : ℝ) : ℂ) := by
      rw [hinv, integral_complex_ofReal]
    rw [integral_complex_ofReal] at h'
    exact_mod_cast h'

  have hCS : ∀ y : AdelicGL2 (𝓞 K) K,
      ‖∫ k, φ ((k : AdelicGL2 (𝓞 K) K) * y) * conj (ψ (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖ ≤
        Real.sqrt Nφ * Real.sqrt Nψ := by
    intro y
    have hcy : Continuous fun g : AdelicGL2 (𝓞 K) K => φ (g * y) := hφc.comp (continuous_mul_right y)
    have := MatrixNormAx.norm_integral_mul_conj_le K (a := fun g => φ (g * y)) (b := ψ) hcy hψc
    rw [hφny y] at this
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact this

  set F : adelicMaximalCompact K → AdelicGL2 (𝓞 K) K → ℂ :=
    fun k y => φ ((k : AdelicGL2 (𝓞 K) K) * y) * f y * conj (ψ (k : AdelicGL2 (𝓞 K) K)) with hFdef
  have hFc : Continuous F.uncurry := by
    have h1 : Continuous fun p : adelicMaximalCompact K × AdelicGL2 (𝓞 K) K =>
        φ ((p.1 : AdelicGL2 (𝓞 K) K) * p.2) :=
      hφc.comp ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)
    have h2 : Continuous fun p : adelicMaximalCompact K × AdelicGL2 (𝓞 K) K => f p.2 := hf.comp continuous_snd
    have h3 : Continuous fun p : adelicMaximalCompact K × AdelicGL2 (𝓞 K) K =>
        conj (ψ (p.1 : AdelicGL2 (𝓞 K) K)) :=
      Complex.continuous_conj.comp (hψc.comp (continuous_subtype_val.comp continuous_fst))
    exact (h1.mul h2).mul h3
  have hFs : HasCompactSupport F.uncurry := by
    refine HasCompactSupport.intro (isCompact_univ.prod hfc) ?_
    rintro ⟨k, y⟩ hky
    have hy : y ∉ tsupport f := fun hy => hky ⟨Set.mem_univ _, hy⟩
    have : f y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [Function.uncurry, hFdef, this]
  have hswap := integral_integral_swap_of_hasCompactSupport (μ := maximalCompactHaar K)
    (ν := adelicGLHaar (Fin 2) (𝓞 K) K) hFc hFs
  have hLHS : (∫ k, rightConv K φ f (k : AdelicGL2 (𝓞 K) K) * conj (ψ (k : AdelicGL2 (𝓞 K) K))
      ∂(maximalCompactHaar K)) = ∫ k, ∫ y, F k y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ∂(maximalCompactHaar K) := by
    congr 1; funext k
    rw [AutomorphicForm.rightConv_apply]
    exact (integral_mul_const _ _).symm
  rw [hLHS, hswap]
  have hbd : ∀ y, ‖∫ k, F k y ∂(maximalCompactHaar K)‖ ≤ ‖f y‖ * (Real.sqrt Nφ * Real.sqrt Nψ) := by
    intro y
    have hinner : (∫ k, F k y ∂(maximalCompactHaar K)) =
        f y * ∫ k, φ ((k : AdelicGL2 (𝓞 K) K) * y) * conj (ψ (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
      rw [← integral_const_mul]
      congr 1; funext k; simp only [hFdef]; ring
    rw [hinner, norm_mul]
    exact mul_le_mul_of_nonneg_left (hCS y) (norm_nonneg _)
  calc ‖∫ y, ∫ k, F k y ∂(maximalCompactHaar K) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖
      ≤ ∫ y, ‖f y‖ * (Real.sqrt Nφ * Real.sqrt Nψ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        norm_integral_le_of_norm_le ((hf.integrable_of_hasCompactSupport hfc).norm.mul_const _)
          (Filter.Eventually.of_forall hbd)
    _ = (∫ y, ‖f y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * Real.sqrt Nφ * Real.sqrt Nψ := by
        rw [integral_mul_const]; ring

open AutomorphicForm in

theorem Ws1.RHSStab.matrix_norm_bound
    (K : Type) [Field K] [NumberField K]
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (m : ℕ) (φ : Fin m → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ j s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ j s))
      (_hφjc : ∀ j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ j p.1 p.2))
      (_hφflat : ∀ j (s : ℂ) (k : adelicMaximalCompact K),
        φ j s (k : AdelicGL2 (𝓞 K) K) = φ j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφon : ∀ i j, ∫ k, φ i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φ j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (t : ℝ) (u v : Fin m → ℂ),
    ‖∑ i : Fin m, ∑ j : Fin m,
        (∫ k, rightConv K (φ j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) *
            conj (φ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          (v j * conj (u i))‖ ≤
      (∫ g, ‖f g‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
        Real.sqrt (∑ i : Fin m, ‖u i‖ ^ (2 : ℕ)) * Real.sqrt (∑ j : Fin m, ‖v j‖ ^ (2 : ℕ)) := by
  intro αm hαm μ ν hμ hν m φ hφ hφjc hφflat hφon t u v
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  have hφc : ∀ (j : Fin m) (s : ℂ), Continuous (φ j s) := fun j s =>
    (hφjc j).comp (continuous_const.prodMk continuous_id)
  have hRc : ∀ j : Fin m, Continuous (rightConv K (φ j ((t : ℂ) * Complex.I)) f) := fun j =>
    AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport K _ (hφc j _) f hf hfc

  have hKint : ∀ (F : AdelicGL2 (𝓞 K) K → ℂ), Continuous F → Integrable (fun k : adelicMaximalCompact K => F (k : AdelicGL2 (𝓞 K) K)) (maximalCompactHaar K) :=
    fun F hF => integrableOn_univ.mp
      (((hF.comp continuous_subtype_val).continuousOn).integrableOn_compact isCompact_univ)

  set Φv : AdelicGL2 (𝓞 K) K → ℂ := fun g => ∑ j : Fin m, v j * φ j ((t : ℂ) * Complex.I) g with hΦv
  set Φu : AdelicGL2 (𝓞 K) K → ℂ := fun g => ∑ i : Fin m, u i * φ i ((t : ℂ) * Complex.I) g with hΦu
  have hΦv_c : Continuous Φv := continuous_finset_sum _ fun j _ => continuous_const.mul (hφc j _)
  have hΦu_c : Continuous Φu := continuous_finset_sum _ fun i _ => continuous_const.mul (hφc i _)
  have hcomb_ind : ∀ (w : Fin m → ℂ), IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I))
      (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) (fun g => ∑ j : Fin m, w j * φ j ((t : ℂ) * Complex.I) g) := by
    intro w b hb g
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hφ j _ b hb g]
    ring
  have hΦv_ind := hcomb_ind v
  have hΦu_ind := hcomb_ind u

  have hRlin : ∀ k : AdelicGL2 (𝓞 K) K, rightConv K Φv f k = ∑ j : Fin m, v j * rightConv K (φ j ((t : ℂ) * Complex.I)) f k := by
    intro k
    have hI : ∀ j : Fin m, Integrable (fun x : AdelicGL2 (𝓞 K) K => φ j ((t : ℂ) * Complex.I) (k * x) * f x)
        (adelicGLHaar (Fin 2) (𝓞 K) K) := fun j =>
      Continuous.integrable_of_hasCompactSupport (((hφc j _).comp (continuous_mul_left k)).mul hf) hfc.mul_left
    simp only [AutomorphicForm.rightConv_apply, hΦv, Finset.sum_mul]
    rw [integral_finset_sum _ (fun j _ => ((hI j).const_mul (v j)).congr (Filter.Eventually.of_forall fun x => by ring))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

  have hpair : ∑ i : Fin m, ∑ j : Fin m,
      (∫ k, rightConv K (φ j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) *
          conj (φ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) * (v j * conj (u i)) =
      ∫ k, rightConv K Φv f (k : AdelicGL2 (𝓞 K) K) * conj (Φu (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    have hIij : ∀ i j : Fin m, Integrable (fun k : adelicMaximalCompact K =>
        rightConv K (φ j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
      fun i j => hKint (fun g : AdelicGL2 (𝓞 K) K => rightConv K (φ j ((t : ℂ) * Complex.I)) f g * conj (φ i ((t : ℂ) * Complex.I) g))
        ((hRc j).mul (Complex.continuous_conj.comp (hφc i _)))
    have hexp : (fun k : adelicMaximalCompact K => rightConv K Φv f (k : AdelicGL2 (𝓞 K) K) * conj (Φu (k : AdelicGL2 (𝓞 K) K))) =
        fun k : adelicMaximalCompact K => ∑ i : Fin m, ∑ j : Fin m, (v j * conj (u i)) *
          (rightConv K (φ j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) := by
      funext k
      rw [hRlin, hΦu]
      simp only [map_sum, map_mul, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hexp, integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => (hIij i j).const_mul _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => (hIij i j).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, mul_comm]

  have hnormsq : ∀ (w : Fin m → ℂ), (∫ k, ‖(∑ j : Fin m, w j * φ j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))‖ ^ (2 : ℕ) ∂(maximalCompactHaar K)) =
      ∑ j : Fin m, ‖w j‖ ^ (2 : ℕ) := by
    intro w
    have hI0 : ∀ i j : Fin m, Integrable (fun k : adelicMaximalCompact K =>
        φ i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φ j 0 (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
      fun i j => hKint (fun g : AdelicGL2 (𝓞 K) K => φ i 0 g * conj (φ j 0 g)) ((hφc i 0).mul (Complex.continuous_conj.comp (hφc j 0)))
    have hC : ((∫ k, ‖(∑ j : Fin m, w j * φ j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))‖ ^ (2 : ℕ) ∂(maximalCompactHaar K) : ℝ) : ℂ) =
        ((∑ j : Fin m, ‖w j‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      have hexp : (fun k : adelicMaximalCompact K =>
          (((‖(∑ j : Fin m, w j * φ j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))‖ ^ (2 : ℕ) : ℝ)) : ℂ)) =
          fun k : adelicMaximalCompact K => ∑ i : Fin m, ∑ j : Fin m, (w i * conj (w j)) * (φ i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φ j 0 (k : AdelicGL2 (𝓞 K) K))) := by
        funext k
        rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
        simp only [hφflat, map_sum, map_mul, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hexp, integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => (hI0 i j).const_mul _))]
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ (fun j _ => (hI0 i j).const_mul _)]
      rw [Finset.sum_eq_single i]
      · rw [integral_const_mul, hφon i i, if_pos rfl, mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      · intro j _ hji
        rw [integral_const_mul, hφon i j, if_neg (Ne.symm hji), mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    exact_mod_cast hC
  have hNv : Real.sqrt (∫ k, ‖Φv (k : AdelicGL2 (𝓞 K) K)‖ ^ (2 : ℕ) ∂(maximalCompactHaar K)) = Real.sqrt (∑ j : Fin m, ‖v j‖ ^ (2 : ℕ)) := by
    rw [hΦv, hnormsq v]
  have hNu : Real.sqrt (∫ k, ‖Φu (k : AdelicGL2 (𝓞 K) K)‖ ^ (2 : ℕ) ∂(maximalCompactHaar K)) = Real.sqrt (∑ i : Fin m, ‖u i‖ ^ (2 : ℕ)) := by
    rw [hΦu, hnormsq u]

  rw [hpair]
  have h := MatrixNormAx.pairing_bound K f hf hfc hαm μ ν hμ hν t Φv Φu hΦv_c hΦu_c hΦv_ind hΦu_ind
  rw [hNv, hNu] at h
  calc _ ≤ _ := h
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
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
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀ (ε : ℝ) (_hε : 0 < ε)
      (X₁ X₂ Y₁ Y₂ : (e : ιE) → Fin (nE e) → ℝ → ℂ),
      ((∀ (e : ιE) (j : Fin (nE e)), MemLp (Y₁ e j) 2) ∧
      Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖Y₁ e j t‖ ^ (2 : ℕ))) → ((∀ (e : ιE) (j : Fin (nE e)), MemLp (Y₂ e j) 2) ∧
      Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖Y₂ e j t‖ ^ (2 : ℕ))) →
      ((∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ => X₁ e j t - Y₁ e j t) 2) ∧
      Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖X₁ e j t - Y₁ e j t‖ ^ (2 : ℕ)) ∧
      ∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e), ‖X₁ e j t - Y₁ e j t‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ)) → ((∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ => X₂ e j t - Y₂ e j t) 2) ∧
      Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖X₂ e j t - Y₂ e j t‖ ^ (2 : ℕ)) ∧
      ∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e), ‖X₂ e j t - Y₂ e j t‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ)) →
      (∀ e : ιE, Integrable (fun t : ℝ => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (X₂ e j t * conj (X₁ e i t)))) ∧
      Summable (fun e : ιE => ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (X₂ e j t * conj (X₁ e i t))) ∧
      (∀ e : ιE, Integrable (fun t : ℝ => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (Y₂ e j t * conj (Y₁ e i t)))) ∧
      Summable (fun e : ιE => ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (Y₂ e j t * conj (Y₁ e i t))) ∧
      ‖(∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (X₂ e j t * conj (X₁ e i t))) -
          (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (Y₂ e j t * conj (Y₁ e i t)))‖ ≤
        (∫ g, ‖f g‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * ε * (Real.sqrt (∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e), ‖X₁ e j t‖ ^ (2 : ℕ)) + Real.sqrt (∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e), ‖X₂ e j t‖ ^ (2 : ℕ)) + ε) := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _ μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu
    hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE f hf hfc _hfF _hfB _hfA ε hε X₁ X₂ Y₁ Y₂ hY₁ hY₂ hD₁ hD₂
  exact Ws1.RHSStab.abstract_stability (ιE := ιE) (n := nE)
    (fun e t i j => ∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) *
        conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
    (∫ g, ‖f g‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) (integral_nonneg fun g => norm_nonneg _)
    (fun e i j => (AutomorphicForm.continuous_integral_rightConv_axis_mul_conj_of_isArchKFinite_family K hαm (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e)
        (φE e i) (hφE e i) (hφEK e i) (hφEf e i) (hφEjc e i) (hφEhol e i) (hφEKu e i)
        (φE e j) (hφE e j) (hφEK e j) (hφEf e j) (hφEjc e j) (hφEhol e j) (hφEKu e j) f hf hfc).aestronglyMeasurable)
    (fun e t u v => Ws1.RHSStab.matrix_norm_bound K f hf hfc hαm (μ e) (ν e) (hμ e) (hν e) (nE e) (φE e)
        (hφE e) (hφEjc e) (hφEflat e) (hφEon e) t u v)
    ε hε X₁ X₂ Y₁ Y₂ hY₁ hY₂ hD₁ hD₂

end S_AutomorphicForm_norm_tsum_integral_sum_rightConv_mul_mul_conj_sub_le_of_tsum_integral_sum_normSq_sub_le
end P2MW
export P2MW.S_AutomorphicForm_norm_tsum_integral_sum_rightConv_mul_mul_conj_sub_le_of_tsum_integral_sum_normSq_sub_le (solution)
