-- Prove2me | solution 1 for AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3f00413a-0ff5-5d5f-938e-17105d8430b8

import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IwasawaShellIndex
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import Theorems.Thm_HaarQuotient_integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer
import Theorems.Thm_AutomorphicForm_mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem
import Theorems.Thm_AutomorphicForm_lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj
import Theorems.Thm_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent
import Theorems.Thm_AutomorphicForm_isLocallyConstant_iwasawaShellIndex_and_measurable
import Theorems.Thm_AutomorphicForm_isClosed_rationalCentreUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_continuous_whittakerCoefficient
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_UnramifiedWhittaker_summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow
import Theorems.Thm_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_RankinSelberg_exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm IsDedekindDomain UnramifiedWhittaker NumberField.TateGlobal
open scoped NNReal ENNReal

namespace EulerUnfold

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section AbstractPeel

variable {G : Type*} [Group G]

theorem comp_out_comp_mk {β : Type*} {H : Subgroup G} {f : G → β}
    (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    (fun q : MulAction.orbitRel.Quotient H G => f q.out) ∘ (Quotient.mk'' : G → _) = f := by
  funext g
  simp only [Function.comp_apply]
  have hq : @Quotient.mk'' G (MulAction.orbitRel H G) g =
      Quotient.mk'' ((Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) :=
    (Quotient.out_eq' _).symm
  obtain ⟨x, hx⟩ := Quotient.exact' hq
  calc f ((Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out)
      = f ((x : G) * (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) := (hfH x x.2 _).symm
    _ = f g := congrArg f hx

variable [MeasurableSpace G]

theorem measurable_comp_out {β : Type*} [MeasurableSpace β] {H : Subgroup G} {f : G → β}
    (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => f q.out := by
  have h := comp_out_comp_mk (H := H) hfH
  rw [measurable_from_quotient, h]
  exact hf

theorem measurableSet_shellZero {H : Subgroup G} {m : G → ℤ} (hm : Measurable m)
    (hmH : ∀ x ∈ H, ∀ g : G, m (x * g) = m g) :
    MeasurableSet {q : MulAction.orbitRel.Quotient H G | m q.out = 0} :=
  (measurable_comp_out hm hmH) (measurableSet_singleton (0 : ℤ))

omit [MeasurableSpace G] in
theorem shellIndex_zpow_mul {m : G → ℤ} {b : G} (hmb : ∀ g : G, m (b * g) = m g + 1)
    (k : ℤ) (g : G) : m (b ^ k * g) = m g + k := by
  induction k using Int.induction_on generalizing g with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, mul_assoc, ih, hmb]; ring
  | pred i ih =>
    have h1 : m (b⁻¹ * g) = m g - 1 := by
      have := hmb (b⁻¹ * g)
      rw [mul_inv_cancel_left] at this
      linarith
    rw [zpow_sub_one, mul_assoc, ih, h1]; ring

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G]

theorem peel_of_shell_relation
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) (D : ℝ≥0) (hD₀ : D ≠ 0)
    (hbD : ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ x, F ⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩ ∂μH = (D : ℝ≥0∞) * ∫⁻ x, F x ∂μH)
    (m : G → ℤ) (hm : Measurable m) (hmH : ∀ x ∈ H, ∀ g : G, m (x * g) = m g)
    (hmb : ∀ g : G, m (b * g) = m g + 1)
    (F : G → ℂ) (hF : Measurable F) (hFH : ∀ x ∈ H, ∀ g : G, F (x * g) = F g)
    (Φ : ℤ → ℂ) (hΦ : Summable fun n : ℤ => (D : ℝ) ^ n * ‖Φ n‖)
    (hrel : ∀ g : G, m g = 0 → ∀ n : ℤ, F (b ^ n * g) = Φ n * F g)
    (hint : IntegrableOn (fun q : MulAction.orbitRel.Quotient H G => F q.out)
      {q | m q.out = 0} (HaarQuotient.measure μ H μH)) :
    Integrable (fun q : MulAction.orbitRel.Quotient H G => F q.out) (HaarQuotient.measure μ H μH) ∧
    (∫ q, F q.out ∂(HaarQuotient.measure μ H μH)) =
      (∑' n : ℤ, ((D : ℝ) : ℂ) ^ n * Φ n) *
        ∫ q in {q : MulAction.orbitRel.Quotient H G | m q.out = 0}, F q.out
          ∂(HaarQuotient.measure μ H μH) := by
  set h : G → ℂ := fun g => F (b ^ (-m g) * g) with hh_def
  have hbN : b ∈ Subgroup.normalizer (H : Set G) := Subgroup.mem_normalizer_iff.mpr hb
  have hmz : ∀ (k : ℤ) (g : G), m (b ^ k * g) = m g + k := shellIndex_zpow_mul hmb
  have hh_meas : Measurable h := by
    have h1 : Measurable fun p : G × ℤ => F (b ^ (-p.2) * p.1) :=
      measurable_from_prod_countable_left (fun n =>
        (hF.comp (measurable_const_mul (b ^ (-n))) : Measurable fun x : G => F (b ^ (-n) * x)))
    exact h1.comp (measurable_id.prodMk hm)
  have hhH : ∀ x ∈ H, ∀ g : G, h (x * g) = h g := by
    intro x hx g
    simp only [hh_def, hmH x hx g]
    have hmem : b ^ (-m g) * x * (b ^ (-m g))⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (H : Set G)).zpow_mem hbN (-m g)) x).mp hx
    calc F (b ^ (-m g) * (x * g))
        = F ((b ^ (-m g) * x * (b ^ (-m g))⁻¹) * (b ^ (-m g) * g)) := by group
      _ = F (b ^ (-m g) * g) := hFH _ hmem _
  have hhb : ∀ g : G, h (b * g) = h g := by
    intro g
    simp only [hh_def, hmb g]
    congr 1
    group
  have hF_eq : ∀ g : G, F g = h g * Φ (m g) := by
    intro g
    have h0 : m (b ^ (-m g) * g) = 0 := by rw [hmz]; ring
    have := hrel (b ^ (-m g) * g) h0 (m g)
    rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul] at this
    rw [this, mul_comm]
  have hS : MeasurableSet {q : MulAction.orbitRel.Quotient H G | m q.out = 0} :=
    measurableSet_shellZero hm hmH
  have hset_eq : ∀ q : MulAction.orbitRel.Quotient H G, m q.out = 0 → h q.out = F q.out := by
    intro q hq; simp only [hh_def, hq, neg_zero, zpow_zero, one_mul]
  have hint' : IntegrableOn (fun q : MulAction.orbitRel.Quotient H G => h q.out)
      {q | m q.out = 0} (HaarQuotient.measure μ H μH) :=
    hint.congr_fun (fun q hq => (hset_eq q hq).symm) hS
  obtain ⟨hint2, heq⟩ :=
    HaarQuotient.integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer
      μ H hH μH b hb D hD₀ hbD m hm hmH hmb h hh_meas hhH hhb hint' Φ hΦ
  have hfun : (fun q : MulAction.orbitRel.Quotient H G => F q.out) =
      fun q => h q.out * Φ (m q.out) := funext fun q => hF_eq q.out
  refine ⟨hfun ▸ hint2, ?_⟩
  calc (∫ q, F q.out ∂(HaarQuotient.measure μ H μH))
      = ∫ q, h q.out * Φ (m q.out) ∂(HaarQuotient.measure μ H μH) := by rw [hfun]
    _ = _ := heq
    _ = _ := by rw [setIntegral_congr_fun hS (fun q hq => hset_eq q hq)]

end AbstractPeel

section AbstractExhaust

variable {G : Type*} [Group G]

theorem invariant_zpow_mul {β : Type*} {m : G → β} {c : G} (hmc : ∀ g : G, m (c * g) = m g)
    (k : ℤ) (g : G) : m (c ^ k * g) = m g := by
  induction k using Int.induction_on generalizing g with
  | zero => simp
  | succ i ih => rw [zpow_add_one, mul_assoc, ih, hmc]
  | pred i ih =>
    have h1 : m (c⁻¹ * g) = m g := by
      have := hmc (c⁻¹ * g)
      rw [mul_inv_cancel_left] at this
      exact this.symm
    rw [zpow_sub_one, mul_assoc, ih, h1]

variable [MeasurableSpace G]

theorem measurableSet_shells {ι : Type*} {H : Subgroup G} (m : ι → G → ℤ) (hm : ∀ i, Measurable (m i))
    (hmH : ∀ i, ∀ x ∈ H, ∀ g : G, m i (x * g) = m i g) (L : Finset ι) :
    MeasurableSet {q : MulAction.orbitRel.Quotient H G | ∀ i ∈ L, m i q.out = 0} := by
  have : {q : MulAction.orbitRel.Quotient H G | ∀ i ∈ L, m i q.out = 0} =
      ⋂ i ∈ L, {q : MulAction.orbitRel.Quotient H G | m i q.out = 0} := by
    ext q; simp
  rw [this]
  exact Finset.measurableSet_biInter L (fun i _ => measurableSet_shellZero (hm i) (hmH i))

omit [Group G] in
theorem measurableSet_shells' {ι : Type*} (m : ι → G → ℤ) (hm : ∀ i, Measurable (m i)) (L : Finset ι) :
    MeasurableSet {g : G | ∀ i ∈ L, m i g = 0} := by
  have : {g : G | ∀ i ∈ L, m i g = 0} = ⋂ i ∈ L, (m i) ⁻¹' {0} := by
    ext g; simp
  rw [this]
  exact Finset.measurableSet_biInter L (fun i _ => hm i (measurableSet_singleton (0 : ℤ)))

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G]

theorem peel_finset
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    {ι : Type*} (b : ι → G) (hb : ∀ (i : ι) (y : G), y ∈ H ↔ b i * y * (b i)⁻¹ ∈ H)
    (D : ι → ℝ≥0) (hD₀ : ∀ i, D i ≠ 0)
    (hbD : ∀ (i : ι) (F : H → ℝ≥0∞), Measurable F →
      ∫⁻ x, F ⟨b i * (x : G) * (b i)⁻¹, (hb i (x : G)).mp x.2⟩ ∂μH = (D i : ℝ≥0∞) * ∫⁻ x, F x ∂μH)
    (m : ι → G → ℤ) (hm : ∀ i, Measurable (m i)) (hmH : ∀ i, ∀ x ∈ H, ∀ g : G, m i (x * g) = m i g)
    (hmb : ∀ (i : ι) (g : G), m i (b i * g) = m i g + 1)
    (hmb' : ∀ (i j : ι), i ≠ j → ∀ g : G, m i (b j * g) = m i g)
    (F : G → ℂ) (hF : Measurable F) (hFH : ∀ x ∈ H, ∀ g : G, F (x * g) = F g)
    (Φ : ι → ℤ → ℂ) (hΦ : ∀ i, Summable fun n : ℤ => (D i : ℝ) ^ n * ‖Φ i n‖)
    (hrel : ∀ (i : ι) (g : G), m i g = 0 → ∀ n : ℤ, F (b i ^ n * g) = Φ i n * F g)
    (hint : Integrable (fun q : MulAction.orbitRel.Quotient H G => F q.out) (HaarQuotient.measure μ H μH))
    (L : Finset ι) :
    (∫ q, F q.out ∂(HaarQuotient.measure μ H μH)) =
      (∏ i ∈ L, ∑' n : ℤ, ((D i : ℝ) : ℂ) ^ n * Φ i n) *
        ∫ q in {q : MulAction.orbitRel.Quotient H G | ∀ i ∈ L, m i q.out = 0}, F q.out
          ∂(HaarQuotient.measure μ H μH) := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | insert i L hi ih =>
    set ν := HaarQuotient.measure μ H μH with hν
    set A : Set G := {g : G | ∀ j ∈ L, m j g = 0} with hA
    set sL : Set (MulAction.orbitRel.Quotient H G) := {q | ∀ j ∈ L, m j q.out = 0} with hsL
    have hAm : MeasurableSet A := measurableSet_shells' m hm L
    have hsLm : MeasurableSet sL := measurableSet_shells m hm hmH L
    set FL : G → ℂ := A.indicator F with hFL
    have hFLm : Measurable FL := hF.indicator hAm
    have hmemA : ∀ x ∈ H, ∀ g : G, (x * g ∈ A ↔ g ∈ A) := by
      intro x hx g
      simp only [hA, Set.mem_setOf_eq, hmH _ x hx]
    have hFLH : ∀ x ∈ H, ∀ g : G, FL (x * g) = FL g := by
      intro x hx g
      simp only [hFL, Set.indicator_apply, hmemA x hx g, hFH x hx g]
    have hmemAb : ∀ (n : ℤ) (g : G), (b i ^ n * g ∈ A ↔ g ∈ A) := by
      intro n g
      simp only [hA, Set.mem_setOf_eq]
      refine forall₂_congr (fun j hj => ?_)
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [invariant_zpow_mul (hmb' j i hji) n g]
    have hrelL : ∀ g : G, m i g = 0 → ∀ n : ℤ, FL (b i ^ n * g) = Φ i n * FL g := by
      intro g hg n
      simp only [hFL, Set.indicator_apply, hmemAb n g]
      split_ifs with h
      · exact hrel i g hg n
      · rw [mul_zero]
    have hFLout : (fun q : MulAction.orbitRel.Quotient H G => FL q.out) =
        sL.indicator (fun q => F q.out) := by
      funext q
      simp only [hFL, hsL, hA, Set.indicator_apply, Set.mem_setOf_eq]
    have hintL : Integrable (fun q : MulAction.orbitRel.Quotient H G => FL q.out) ν := by
      rw [hFLout]; exact hint.indicator hsLm
    obtain ⟨-, hpeel⟩ := peel_of_shell_relation μ H hH μH (b i) (hb i) (D i) (hD₀ i) (hbD i) (m i) (hm i) (hmH i)
      (hmb i) FL hFLm hFLH (Φ i) (hΦ i) hrelL hintL.integrableOn
    have h1 : (∫ q in sL, F q.out ∂ν) = ∫ q, FL q.out ∂ν := by
      rw [hFLout, integral_indicator hsLm]
    have h2 : (∫ q in {q : MulAction.orbitRel.Quotient H G | m i q.out = 0}, FL q.out ∂ν) =
        ∫ q in {q : MulAction.orbitRel.Quotient H G | ∀ j ∈ insert i L, m j q.out = 0}, F q.out ∂ν := by
      have hset : {q : MulAction.orbitRel.Quotient H G | m i q.out = 0} ∩ sL =
          {q : MulAction.orbitRel.Quotient H G | ∀ j ∈ insert i L, m j q.out = 0} := by
        ext q
        simp [hsL]
      rw [hFLout, setIntegral_indicator hsLm, hset]
    rw [ih, h1, hpeel, h2, Finset.prod_insert hi]
    ring

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] in

theorem tendsto_setIntegral_shells {ι : Type*} [Countable ι] {H : Subgroup G}
    (ν : Measure (MulAction.orbitRel.Quotient H G))
    (m : ι → G → ℤ) (hm : ∀ i, Measurable (m i)) (hmH : ∀ i, ∀ x ∈ H, ∀ g : G, m i (x * g) = m i g)
    (F : G → ℂ) (hint : Integrable (fun q : MulAction.orbitRel.Quotient H G => F q.out) ν) :
    Filter.Tendsto (fun L : Finset ι =>
        ∫ q in {q : MulAction.orbitRel.Quotient H G | ∀ i ∈ L, m i q.out = 0}, F q.out ∂ν)
      Filter.atTop (nhds (∫ q in {q : MulAction.orbitRel.Quotient H G | ∀ i, m i q.out = 0}, F q.out ∂ν)) := by
  have hS : {q : MulAction.orbitRel.Quotient H G | ∀ i, m i q.out = 0} =
      ⋂ L : Finset ι, {q : MulAction.orbitRel.Quotient H G | ∀ i ∈ L, m i q.out = 0} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h L i _; exact h i
    · intro h i; exact h {i} i (Finset.mem_singleton_self i)
  rw [hS]
  apply tendsto_setIntegral_of_antitone (fun L => measurableSet_shells m hm hmH L)
  · intro L L' hLL' q hq j hj
    exact hq j (hLL' hj)
  · exact ⟨∅, hint.integrableOn⟩

end AbstractExhaust

section Algebra

variable (K : Type) [Field K] [NumberField K]

theorem heckeGen_coe (v : HeightOneSpectrum (𝓞 K)) :
    ((heckeGen (𝓞 K) K v : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      Matrix.diagonal ![((uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1] :=
  rfl

theorem heckeGen_mem_adelicBorel (v : HeightOneSpectrum (𝓞 K)) :
    heckeGen (𝓞 K) K v ∈ adelicBorel (𝓞 K) K := by
  show ((heckeGen (𝓞 K) K v : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0
  rw [heckeGen_coe]
  simp

theorem borelDiagFst_heckeGen (v : HeightOneSpectrum (𝓞 K)) :
    borelDiagFst (⟨heckeGen (𝓞 K) K v, heckeGen_mem_adelicBorel K v⟩ : ↥(adelicBorel (𝓞 K) K)) =
      uniformizerIdele K v := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show ((heckeGen (𝓞 K) K v : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = _
  rw [heckeGen_coe]
  simp

theorem borelDiagSnd_heckeGen (v : HeightOneSpectrum (𝓞 K)) :
    borelDiagSnd (⟨heckeGen (𝓞 K) K v, heckeGen_mem_adelicBorel K v⟩ : ↥(adelicBorel (𝓞 K) K)) = 1 := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show ((heckeGen (𝓞 K) K v : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = _
  rw [heckeGen_coe]
  simp

theorem det_heckeGen (v : HeightOneSpectrum (𝓞 K)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v) = uniformizerIdele K v := by
  rw [det_borel_eq_diag_mul (heckeGen_mem_adelicBorel K v), borelDiagFst_heckeGen,
    borelDiagSnd_heckeGen, mul_one]

theorem centralScalar_coe (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((centralScalar (𝓞 K) K z : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) :=
  rfl

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K z * g = g * centralScalar (𝓞 K) K z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, centralScalar_coe]
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 K) K) (Commute.all _) _).eq

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, centralScalar_coe, Matrix.scalar_apply, Matrix.det_diagonal,
    Units.val_mul]
  simp [pow_two]

theorem globalPoints_scalar (a : Kˣ) :
    globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a) =
      centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) a) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply, centralScalar_coe]
  show algebraMap K (AdeleRing (𝓞 K) K) (Matrix.scalar (Fin 2) (a : K) i j) =
    Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem det_unipotentGL2 (t : AdeleRing (𝓞 K) K) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 t : AdelicGL2 (𝓞 K) K) = 1 := by
  rw [det_borel_eq_diag_mul (unipotentGL2_mem_borelSubgroup t), borelDiagFst_unipotentGL2,
    borelDiagSnd_unipotentGL2, mul_one]

theorem ideleNorm_zpow (z : (AdeleRing (𝓞 K) K)ˣ) (n : ℤ) : ideleNorm K (z ^ n) = ideleNorm K z ^ n := by
  simp only [ideleNorm, map_zpow, NNReal.coe_zpow]

theorem ideleNorm_pow (z : (AdeleRing (𝓞 K) K)ˣ) (n : ℕ) : ideleNorm K (z ^ n) = ideleNorm K z ^ n := by
  simp only [ideleNorm, map_pow, NNReal.coe_pow]

end Algebra

section Covariance

variable (K : Type) [Field K] [NumberField K]

theorem whittakerCoefficient_centralScalar_mul (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((ω z : ℂˣ) : ℂ) * x g)
    (α : K) (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ x α (centralScalar (𝓞 K) K z * g) =
      ((ω z : ℂˣ) : ℂ) * whittakerCoefficient K pins ψ x α g := by
  letI := pins.nS
  simp only [whittakerCoefficient]
  rw [← integral_const_mul]
  congr 1
  funext t
  rw [← mul_assoc, ← centralScalar_comm K z (unipotentGL2 t), mul_assoc, hxZ, mul_assoc]

theorem whittakerCoefficient_rationalCentre_mul (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      x (globalPoints (𝓞 K) K γ * g) = x g)
    (α : K) (a : Kˣ) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ x α
        (globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
          * g) =
      whittakerCoefficient K pins ψ x α g := by
  letI := pins.nS
  simp only [whittakerCoefficient]
  congr 1
  funext t
  rw [← mul_assoc, globalPoints_scalar, ← centralScalar_comm K _ (unipotentGL2 t), mul_assoc,
    ← globalPoints_scalar, hxG]

theorem inducedSection_centralScalar_mul
    (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (s : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    φ (centralScalar (𝓞 K) K z * g) = ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * φ g := by
  rw [isInducedSection_centralScalar_mul hφ, ← Units.val_mul, etaFst_mul_etaSnd, Units.val_mul]

theorem inducedSection_heckeGen_mul
    (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (s : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) :
    φ (heckeGen (𝓞 K) K v * g) =
      ((μ (uniformizerIdele K v) : ℂˣ) : ℂ) *
        ((((α (uniformizerIdele K v) : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2)) * φ g := by
  rw [hφ _ (heckeGen_mem_adelicBorel K v) g, borelDiagFst_heckeGen, borelDiagSnd_heckeGen, map_one,
    Units.val_one, mul_one, etaFst_apply, Units.val_mul, cpowChar_apply_val]

theorem inducedSection_heckeGen_pow_mul
    (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (s : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) (g : AdelicGL2 (𝓞 K) K) :
    φ (heckeGen (𝓞 K) K v ^ k * g) =
      (((μ (uniformizerIdele K v) : ℂˣ) : ℂ) *
        ((((α (uniformizerIdele K v) : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2))) ^ k * φ g := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, inducedSection_heckeGen_mul K μ ν α hα s φ hφ, ih, pow_succ]
    ring

end Covariance

section Integrand

variable (K : Type) [Field K] [NumberField K]

theorem quotientIntegrand_apply (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (x y φ : AdelicGL2 (𝓞 K) K → ℂ) (w d₁ d₂ : ℝ) (g : AdelicGL2 (𝓞 K) K) :
    RankinSelberg.quotientIntegrand K pins ψ x y φ w d₁ d₂ g =
      (if ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂ then (1 : ℂ) else 0) *
        (whittakerCoefficient K pins ψ x 1 g * (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 g)) *
        φ g * ((ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ) := by
  simp only [RankinSelberg.quotientIntegrand, Set.indicator_apply, Set.mem_setOf_eq]
  ring

theorem quotientIntegrand_eq_mul_of (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (x y φ : AdelicGL2 (𝓞 K) K → ℂ) (w d₁ d₂ : ℝ) (g g' : AdelicGL2 (𝓞 K) K) (c₁ c₂ : ℂ)
    (hdet : ideleNorm K (Matrix.GeneralLinearGroup.det g') = ideleNorm K (Matrix.GeneralLinearGroup.det g))
    (hW : whittakerCoefficient K pins ψ x 1 g' * (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 g') =
      c₁ * (whittakerCoefficient K pins ψ x 1 g * (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 g)))
    (hφ : φ g' = c₂ * φ g) :
    RankinSelberg.quotientIntegrand K pins ψ x y φ w d₁ d₂ g' =
      c₁ * c₂ * RankinSelberg.quotientIntegrand K pins ψ x y φ w d₁ d₂ g := by
  rw [quotientIntegrand_apply, quotientIntegrand_apply, hdet, hW, hφ]
  ring

theorem measurable_quotientIntegrand
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : Continuous ψ)
    (x y φ : AdelicGL2 (𝓞 K) K → ℂ) (hx : Continuous x) (hy : Continuous y) (hφ : Continuous φ)
    (w d₁ d₂ : ℝ) :
    Measurable (RankinSelberg.quotientIntegrand K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂) := by
  have hN : Measurable fun g : AdelicGL2 (𝓞 K) K => ideleNorm K (Matrix.GeneralLinearGroup.det g) :=
    (continuous_ideleNorm_det K).measurable
  have hWx := (continuous_whittakerCoefficient K D U gen ψ hψ x hx 1).measurable
  have hWy := (continuous_whittakerCoefficient K D U gen ψ hψ y hy 1).measurable
  have hI : Measurable fun g : AdelicGL2 (𝓞 K) K =>
      ({g : AdelicGL2 (𝓞 K) K | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
        (fun _ => (1 : ℂ)) g) :=
    measurable_const.indicator (hN measurableSet_Icc)
  have hP : Measurable fun g : AdelicGL2 (𝓞 K) K => ((ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (hN.pow_const (-w))
  unfold RankinSelberg.quotientIntegrand
  exact (((hI.mul hWx).mul (Complex.continuous_conj.measurable.comp hWy)).mul hφ.measurable).mul hP

end Integrand

section HInvariance

variable (K : Type) [Field K] [NumberField K]

def leftStabilizer (f : AdelicGL2 (𝓞 K) K → ℂ) : Subgroup (AdelicGL2 (𝓞 K) K) where
  carrier := {x | ∀ g, f (x * g) = f g}
  mul_mem' := by
    intro a b ha hb g
    rw [mul_assoc, ha, hb]
  one_mem' := by
    intro g
    rw [one_mul]
  inv_mem' := by
    intro a ha g
    rw [← ha (a⁻¹ * g), mul_inv_cancel_left]

theorem globalPoints_unipotentGL2 (β : K) :
    globalPoints (𝓞 K) K (unipotentGL2 β) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem whittakerCoefficient_one_unipotentGL2_mul
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hfG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      f (globalPoints (𝓞 K) K γ * g) = f g)
    (t : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ f 1 (unipotentGL2 t * g) =
      ψ t * whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ f 1 g := by
  have hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K),
      f (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * g) = f (unipotentGL2 u * g) := by
    intro β u
    rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hfG]
  have h := whittakerCoefficient_unipotentGL2_mul K D U gen ψ hψ.principalInvariant f g hper 1 t
  rw [map_one, one_mul] at h
  exact h

theorem quotientIntegrand_unipotentGL2_mul
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (x y φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      x (globalPoints (𝓞 K) K γ * g) = x g)
    (hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      y (globalPoints (𝓞 K) K γ * g) = y g)
    (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) (w d₁ d₂ : ℝ)
    (t : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    RankinSelberg.quotientIntegrand K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂
        (unipotentGL2 t * g) =
      RankinSelberg.quotientIntegrand K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ g := by
  have hψ1 : ψ t * (starRingEnd ℂ) (ψ t) = 1 := by
    rw [Complex.mul_conj', NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar K hψ t]
    simp
  have h := quotientIntegrand_eq_mul_of K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ g
    (unipotentGL2 t * g) 1 1
    (by rw [map_mul, ideleNorm_mul, det_unipotentGL2]; simp [ideleNorm])
    (by
      rw [whittakerCoefficient_one_unipotentGL2_mul K D U gen ψ hψ x hxG,
        whittakerCoefficient_one_unipotentGL2_mul K D U gen ψ hψ y hyG, map_mul]
      linear_combination
        (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 g *
          (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1 g)) * hψ1)
    (by rw [isInducedSection_unipotent_mul hφ, one_mul])
  rw [h, one_mul, one_mul]

theorem quotientIntegrand_rationalCentre_mul
    (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (s : ℂ) (hμF : IsIdeleClassChar (𝓞 K) K μ) (hνF : IsIdeleClassChar (𝓞 K) K ν)
    (x y φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      x (globalPoints (𝓞 K) K γ * g) = x g)
    (hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      y (globalPoints (𝓞 K) K γ * g) = y g)
    (hφ : IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ) (w d₁ d₂ : ℝ)
    (a : Kˣ) (g : AdelicGL2 (𝓞 K) K) :
    RankinSelberg.quotientIntegrand K pins ψ x y φ w d₁ d₂
        (globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
          * g) =
      RankinSelberg.quotientIntegrand K pins ψ x y φ w d₁ d₂ g := by
  have h := quotientIntegrand_eq_mul_of K pins ψ x y φ w d₁ d₂ g
    (globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)
      * g) 1 1
    (by rw [map_mul, ideleNorm_mul, ideleNorm_det_globalPoints, one_mul])
    (by
      rw [whittakerCoefficient_rationalCentre_mul K pins ψ x hxG, whittakerCoefficient_rationalCentre_mul K pins ψ y hyG,
        one_mul])
    (by
      rw [globalPoints_scalar, inducedSection_centralScalar_mul K μ ν α hα s φ hφ, hμF a, hνF a, Units.val_one,
        one_mul])
  rw [h, one_mul, one_mul]

theorem quotientIntegrand_mul_of_mem_rationalCentreUnipotent
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (s : ℂ) (hμF : IsIdeleClassChar (𝓞 K) K μ) (hνF : IsIdeleClassChar (𝓞 K) K ν)
    (x y φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      x (globalPoints (𝓞 K) K γ * g) = x g)
    (hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      y (globalPoints (𝓞 K) K γ * g) = y g)
    (hφ : IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ) (w d₁ d₂ : ℝ)
    (h : AdelicGL2 (𝓞 K) K) (hh : h ∈ rationalCentreUnipotent K) (g : AdelicGL2 (𝓞 K) K) :
    RankinSelberg.quotientIntegrand K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ (h * g) =
      RankinSelberg.quotientIntegrand K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ g := by
  have hle : rationalCentreUnipotent K ≤
      leftStabilizer K (RankinSelberg.quotientIntegrand K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂) := by
    apply sup_le
    · rintro _ ⟨a, rfl⟩ g'
      exact quotientIntegrand_rationalCentre_mul K _ ψ μ ν α hα s hμF hνF x y φ hxG hyG hφ w d₁ d₂ a g'
    · rintro _ ⟨t, rfl⟩ g'
      exact quotientIntegrand_unipotentGL2_mul K D U gen ψ hψ _ _ x y φ hxG hyG hφ w d₁ d₂ t.toAdd g'
  exact hle hh g

end HInvariance

section ShellRelation

variable (K : Type) [Field K] [NumberField K]

def shellWeight (C : ℂ) (ux uy : ℕ → ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then C ^ n.toNat * (ux n.toNat * uy n.toNat) else 0

@[scoped simp] theorem shellWeight_natCast (C : ℂ) (ux uy : ℕ → ℂ) (k : ℕ) :
    shellWeight C ux uy (k : ℤ) = C ^ k * (ux k * uy k) := by
  simp [shellWeight]

@[scoped simp] theorem shellWeight_negSucc (C : ℂ) (ux uy : ℕ → ℂ) (k : ℕ) :
    shellWeight C ux uy (Int.negSucc k) = 0 := by
  simp [shellWeight]

theorem whittakerProduct_centralScalar_mul (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (x y : AdelicGL2 (𝓞 K) K → ℂ) (ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
    (hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
    (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ x 1 (centralScalar (𝓞 K) K z * g) *
        (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 (centralScalar (𝓞 K) K z * g)) =
      (((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ)) *
        (whittakerCoefficient K pins ψ x 1 g * (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 g)) := by
  rw [whittakerCoefficient_centralScalar_mul K pins ψ x ωx hxZ 1 z g,
    whittakerCoefficient_centralScalar_mul K pins ψ y ωy hyZ 1 z g, map_mul]
  ring

theorem heckeGen_mul_centralScalar_pow (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) (k : ℕ) :
    (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) ^ k =
      centralScalar (𝓞 K) K (u ^ k) * heckeGen (𝓞 K) K v ^ k := by
  have hc : Commute (heckeGen (𝓞 K) K v) (centralScalar (𝓞 K) K u) :=
    (centralScalar_comm K u (heckeGen (𝓞 K) K v)).symm
  rw [hc.mul_pow, ← map_pow]
  exact (centralScalar_comm K (u ^ k) _).symm

theorem quotientIntegrand_shift_zpow_mul
    (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (μ ν ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (hαn : ∀ t, ((α t : ℝˣ) : ℝ) = ideleNorm K t) (w : ℝ)
    (hZ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
        ((ideleNorm K z ^ (2 * w) : ℝ) : ℂ))
    (s : ℂ) (x y φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
    (hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
    (hφ : IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ) (d₁ d₂ : ℝ)
    (v : HeightOneSpectrum (𝓞 K)) (ux uy : ℕ → ℂ)
    (hP : ∀ g : AdelicGL2 (𝓞 K) K, iwasawaShellIndex K v g = 0 → ∀ m : ℕ,
      whittakerCoefficient K pins ψ x 1 (heckeGen (𝓞 K) K v ^ m * g) *
          (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 (heckeGen (𝓞 K) K v ^ m * g)) =
        ux m * uy m *
          (whittakerCoefficient K pins ψ x 1 g * (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 g)))
    (hPneg : ∀ g : AdelicGL2 (𝓞 K) K, iwasawaShellIndex K v g = 0 → ∀ m : ℕ, 0 < m →
      whittakerCoefficient K pins ψ x 1 ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) *
          (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g)) = 0)
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : ideleNorm K u = Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ))
    (hϖ : ideleNorm K (uniformizerIdele K v) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹)
    (hN : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0)
    (g : AdelicGL2 (𝓞 K) K) (hg : iwasawaShellIndex K v g = 0) (n : ℤ) :
    RankinSelberg.quotientIntegrand K pins ψ x y φ w d₁ d₂
        ((heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) ^ n * g) =
      shellWeight
          ((((Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)) ^ (2 * w) : ℝ) : ℂ) *
            (((μ (uniformizerIdele K v) : ℂˣ) : ℂ) *
              ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2)))
          ux uy n *
        RankinSelberg.quotientIntegrand K pins ψ x y φ w d₁ d₂ g := by
  set N : ℕ := Ideal.absNorm v.asIdeal with hN_def
  have hNr : ((N : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  set b := heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u with hb_def
  have hdetb : ideleNorm K (Matrix.GeneralLinearGroup.det b) = 1 := by
    rw [hb_def, map_mul, ideleNorm_mul, det_heckeGen, det_centralScalar, ideleNorm_mul, hϖ, hu,
      Real.mul_self_sqrt (Nat.cast_nonneg _), inv_mul_cancel₀ hNr]
  have hdet : ∀ n : ℤ, ideleNorm K (Matrix.GeneralLinearGroup.det (b ^ n * g)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det g) := by
    intro n
    rw [map_mul, ideleNorm_mul, map_zpow, ideleNorm_zpow, hdetb, one_zpow, one_mul]
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [shellWeight_natCast, zpow_natCast, hb_def, heckeGen_mul_centralScalar_pow, mul_assoc]
    have hW1 := whittakerProduct_centralScalar_mul K pins ψ x y ωx ωy hxZ hyZ (u ^ k) (heckeGen (𝓞 K) K v ^ k * g)
    have hW2 := hP g hg k
    have hφ1 := inducedSection_centralScalar_mul K μ ν α hα s φ hφ (u ^ k) (heckeGen (𝓞 K) K v ^ k * g)
    have hφ2 := inducedSection_heckeGen_pow_mul K μ ν α hα s φ hφ v k g
    have hdet' : ideleNorm K (Matrix.GeneralLinearGroup.det
        (centralScalar (𝓞 K) K (u ^ k) * (heckeGen (𝓞 K) K v ^ k * g))) =
        ideleNorm K (Matrix.GeneralLinearGroup.det g) := by
      have := hdet (k : ℤ)
      rwa [zpow_natCast, hb_def, heckeGen_mul_centralScalar_pow, mul_assoc] at this
    rw [quotientIntegrand_eq_mul_of K pins ψ x y φ w d₁ d₂ g _
      ((((ωx (u ^ k) : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy (u ^ k) : ℂˣ) : ℂ)) * (ux k * uy k))
      ((((μ (u ^ k) : ℂˣ) : ℂ) * ((ν (u ^ k) : ℂˣ) : ℂ)) *
        (((μ (uniformizerIdele K v) : ℂˣ) : ℂ) *
          ((((α (uniformizerIdele K v) : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2))) ^ k)
      hdet' (by rw [hW1, hW2]; ring) (by rw [hφ1, hφ2]; ring)]
    have hZk := hZ (u ^ k)
    rw [ideleNorm_pow, hu] at hZk
    have hr : ((Real.sqrt ((N : ℕ) : ℝ) ^ k) ^ (2 * w) : ℝ) = (Real.sqrt ((N : ℕ) : ℝ) ^ (2 * w)) ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.sqrt_nonneg _), mul_comm, Real.rpow_mul (Real.sqrt_nonneg _),
        Real.rpow_natCast]
    rw [hr] at hZk
    rw [hαn, hϖ]
    congr 1
    calc (((ωx (u ^ k) : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy (u ^ k) : ℂˣ) : ℂ)) * (ux k * uy k) *
          ((((μ (u ^ k) : ℂˣ) : ℂ) * ((ν (u ^ k) : ℂˣ) : ℂ)) *
            (((μ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((((N : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2)) ^ k)
        = (((ωx (u ^ k) : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy (u ^ k) : ℂˣ) : ℂ) * ((μ (u ^ k) : ℂˣ) : ℂ) *
            ((ν (u ^ k) : ℂˣ) : ℂ)) *
            (((μ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((((N : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2)) ^ k *
            (ux k * uy k) := by ring
      _ = _ := by rw [hZk]; push_cast; ring
  · obtain ⟨k, rfl⟩ := Int.eq_negSucc_of_lt_zero (not_le.mp hn)
    rw [shellWeight_negSucc, zero_mul, zpow_negSucc, hb_def, heckeGen_mul_centralScalar_pow, mul_inv_rev, ← map_inv,
      ← inv_pow, ← centralScalar_comm, mul_assoc, quotientIntegrand_apply,
      whittakerProduct_centralScalar_mul K pins ψ x y ωx ωy hxZ hyZ, hPneg g hg (k + 1) (Nat.succ_pos k)]
    simp

end ShellRelation

section LocalFactor

open LanglandsTunnell.RankinSelberg UnramifiedWhittaker Polynomial

theorem eval_rsEulerPoly_scale {R : Type*} [CommRing R] (a b a' b' c t : R) :
    (rsEulerPoly (c * a) (c ^ 2 * b) a' b' 0).eval t = (rsEulerPoly a b a' b' 0).eval (c * t) := by
  simp only [rsEulerPoly, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

theorem summable_and_tsum_shellWeight (N : ℝ) (hN : 0 < N) (C : ℂ) (ux uy : ℕ → ℂ)
    (hs : Summable fun k : ℕ => ‖ux k * uy k * ((N : ℂ) * C) ^ k‖) :
    Summable (fun n : ℤ => N ^ n * ‖shellWeight C ux uy n‖) ∧
      ∑' n : ℤ, ((N : ℝ) : ℂ) ^ n * shellWeight C ux uy n = ∑' k : ℕ, ux k * uy k * ((N : ℂ) * C) ^ k := by
  have key : ∀ n : ℤ, n ∉ Set.range (Nat.cast : ℕ → ℤ) → shellWeight C ux uy n = 0 := by
    intro n hn
    have : ¬ 0 ≤ n := fun h0 => hn ⟨n.toNat, Int.toNat_of_nonneg h0⟩
    simp [shellWeight, this]
  have hsupp1 : ∀ n ∉ Set.range (Nat.cast : ℕ → ℤ), (fun n : ℤ => N ^ n * ‖shellWeight C ux uy n‖) n = 0 := by
    intro n hn
    simp [key n hn]
  have hsupp2 : Function.support (fun n : ℤ => ((N : ℝ) : ℂ) ^ n * shellWeight C ux uy n) ⊆
      Set.range (Nat.cast : ℕ → ℤ) := by
    intro n hn
    by_contra h
    exact hn (by simp [key n h])
  have h1 : (fun n : ℤ => N ^ n * ‖shellWeight C ux uy n‖) ∘ (Nat.cast : ℕ → ℤ) =
      fun k => ‖ux k * uy k * ((N : ℂ) * C) ^ k‖ := by
    funext k
    simp only [Function.comp_apply, zpow_natCast, shellWeight_natCast, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hN]
    ring
  have h2 : (fun n : ℤ => ((N : ℝ) : ℂ) ^ n * shellWeight C ux uy n) ∘ (Nat.cast : ℕ → ℤ) =
      fun k => ux k * uy k * ((N : ℂ) * C) ^ k := by
    funext k
    simp only [Function.comp_apply, zpow_natCast, shellWeight_natCast]
    ring
  refine ⟨(Nat.cast_injective.summable_iff hsupp1).mp (h1 ▸ hs), ?_⟩
  rw [← Nat.cast_injective.tsum_eq hsupp2]
  exact congrArg tsum h2

theorem local_param_eq (N : ℕ) (hN : 0 < N) (w : ℝ) (s m : ℂ) :
    ((N : ℝ) : ℂ) * ((((Real.sqrt (N : ℝ)) ^ (2 * w) : ℝ) : ℂ) * (m * ((((N : ℝ))⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2))) =
      m * ((N : ℂ) ^ ((1 / 2 + w : ℂ) - s)) := by
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN0 : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : (Real.sqrt (N : ℝ)) ^ (2 * w) = (N : ℝ) ^ w := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNr]
    congr 1
    ring
  have h2 : ((((N : ℝ)) ^ w : ℝ) : ℂ) = ((N : ℝ) : ℂ) ^ (w : ℂ) := Complex.ofReal_cpow hNr w
  have h3 : ((((N : ℝ))⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2) = (((N : ℝ) : ℂ) ^ (s + 1 / 2))⁻¹ := by
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ ?_]
    rw [Complex.arg_ofReal_of_nonneg hNr]
    exact Real.pi_ne_zero.symm
  have h4 : ((N : ℂ)) = ((N : ℝ) : ℂ) := by norm_cast
  rw [h1, h2, h3, h4, ← Complex.cpow_neg]
  calc ((N : ℝ) : ℂ) * (((N : ℝ) : ℂ) ^ (w : ℂ) * (m * ((N : ℝ) : ℂ) ^ (-(s + 1 / 2))))
      = m * (((N : ℝ) : ℂ) ^ (1 : ℂ) * ((N : ℝ) : ℂ) ^ (w : ℂ) * ((N : ℝ) : ℂ) ^ (-(s + 1 / 2))) := by
        rw [Complex.cpow_one]; ring
    _ = m * ((N : ℝ) : ℂ) ^ ((1 : ℂ) + w + -(s + 1 / 2)) := by
        rw [Complex.cpow_add _ _ hN0, Complex.cpow_add _ _ hN0]
    _ = m * ((N : ℝ) : ℂ) ^ ((1 / 2 + w : ℂ) - s) := by
        congr 2
        ring

theorem tsum_shellWeight_eq_localFactor (N : ℕ) (hN : 0 < N) (w : ℝ) (s m lx ox ly oy : ℂ)
    (hsum : Summable fun k : ℕ =>
      heckeRecursionSeq N lx ox k * heckeRecursionSeq N ly oy k * (m * (N : ℂ) ^ ((1 / 2 + w : ℂ) - s)) ^ k)
    (hden : (rsEulerPoly lx ((N : ℂ) * ox) ly ((N : ℂ) * oy) 0).eval
      ((m * (N : ℂ) ^ ((1 / 2 + w : ℂ) - s)) / (N : ℂ) ^ 2) ≠ 0) :
    Summable (fun n : ℤ => (N : ℝ) ^ n *
        ‖shellWeight ((((Real.sqrt (N : ℝ)) ^ (2 * w) : ℝ) : ℂ) * (m * ((((N : ℝ))⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2)))
          (heckeRecursionSeq N lx ox) (heckeRecursionSeq N ly oy) n‖) ∧
    ∑' n : ℤ, (((N : ℕ) : ℝ) : ℂ) ^ n *
        shellWeight ((((Real.sqrt (N : ℝ)) ^ (2 * w) : ℝ) : ℂ) * (m * ((((N : ℝ))⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2)))
          (heckeRecursionSeq N lx ox) (heckeRecursionSeq N ly oy) n =
      (1 - ox * oy * ((m * (N : ℂ) ^ ((1 / 2 + w : ℂ) - s)) / (N : ℂ)) ^ 2) /
        (rsEulerPoly lx ((N : ℂ) * ox) ly ((N : ℂ) * oy) 0).eval
          ((m * (N : ℂ) ^ ((1 / 2 + w : ℂ) - s)) / (N : ℂ) ^ 2) := by
  set C : ℂ := (((Real.sqrt (N : ℝ)) ^ (2 * w) : ℝ) : ℂ) * (m * ((((N : ℝ))⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2)) with hC
  have hy : ((N : ℝ) : ℂ) * C = m * (N : ℂ) ^ ((1 / 2 + w : ℂ) - s) := local_param_eq N hN w s m
  have hy' : ((N : ℕ) : ℂ) * C = m * (N : ℂ) ^ ((1 / 2 + w : ℂ) - s) := by
    rw [← hy]; norm_cast
  have hs' : Summable fun k : ℕ =>
      ‖heckeRecursionSeq N lx ox k * heckeRecursionSeq N ly oy k * ((((N : ℕ) : ℝ) : ℂ) * C) ^ k‖ := by
    have : (((N : ℕ) : ℝ) : ℂ) = ((N : ℕ) : ℂ) := by norm_cast
    rw [this, hy']
    exact summable_norm_iff.mpr hsum
  obtain ⟨h1, h2⟩ := summable_and_tsum_shellWeight ((N : ℕ) : ℝ) (Nat.cast_pos.mpr hN) C
    (heckeRecursionSeq N lx ox) (heckeRecursionSeq N ly oy) hs'
  refine ⟨h1, ?_⟩
  rw [h2]
  have : (((N : ℕ) : ℝ) : ℂ) = ((N : ℕ) : ℂ) := by norm_cast
  rw [this, hy']
  have hC3 := tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval (N : ℂ) lx ox ly oy
    (Nat.cast_ne_zero.mpr hN.ne') (m * (N : ℂ) ^ ((1 / 2 + w : ℂ) - s)) hsum
  exact eq_div_of_mul_eq hden hC3

theorem summable_heckeSeries_of_lt_re (N : ℕ) (hN2 : 2 ≤ N) (κ w : ℝ) (s : ℂ) (lx ox ly oy m : ℂ)
    (hm : ‖m‖ = 1)
    (hbd : ‖lx‖ ≤ (N : ℝ) ^ κ ∧ ‖ox‖ ≤ (N : ℝ) ^ κ ∧ ‖ly‖ ≤ (N : ℝ) ^ κ ∧ ‖oy‖ ≤ (N : ℝ) ^ κ)
    (hs : w + 2 * max κ 0 + 7 / 2 < s.re) :
    Summable fun k : ℕ =>
      heckeRecursionSeq N lx ox k * heckeRecursionSeq N ly oy k * (m * (N : ℂ) ^ ((1 / 2 + w : ℂ) - s)) ^ k := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hN2)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hN2)
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNne : ((N : ℝ)) ≠ 0 := hNpos.ne'
  set T : ℝ := (N : ℝ) ^ (max κ 0 + 1) with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow hN1 (by positivity)
  have hκT : (N : ℝ) ^ κ ≤ T := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_max_left κ 0])
  have hκT' : (N : ℝ) * (N : ℝ) ^ κ ≤ T := by
    calc (N : ℝ) * (N : ℝ) ^ κ ≤ (N : ℝ) * (N : ℝ) ^ (max κ 0) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left κ 0)) hNpos.le
      _ = T := by rw [hT, Real.rpow_add_one hNne, mul_comm]
  have hM : max 1 (‖lx‖ + ‖(N : ℂ) * ox‖) ≤ 2 * T := by
    apply max_le (by linarith)
    rw [norm_mul, Complex.norm_natCast]
    have : (N : ℝ) * ‖ox‖ ≤ T := le_trans (mul_le_mul_of_nonneg_left hbd.2.1 hNpos.le) hκT'
    linarith [hbd.1.trans hκT]
  have hM' : max 1 (‖ly‖ + ‖(N : ℂ) * oy‖) ≤ 2 * T := by
    apply max_le (by linarith)
    rw [norm_mul, Complex.norm_natCast]
    have : (N : ℝ) * ‖oy‖ ≤ T := le_trans (mul_le_mul_of_nonneg_left hbd.2.2.2 hNpos.le) hκT'
    linarith [hbd.2.2.1.trans hκT]
  have hy : ‖m * (N : ℂ) ^ ((1 / 2 + w : ℂ) - s)‖ = (N : ℝ) ^ (1 / 2 + w - s.re) := by
    rw [norm_mul, hm, one_mul, Complex.norm_natCast_cpow_of_pos (lt_of_lt_of_le (by norm_num) hN2)]
    congr 1
    simp
  apply summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow (N : ℂ) lx ox ly oy
    (by exact_mod_cast hNpos.ne') _
  rw [hy, Complex.norm_natCast]
  have hTT : T * T = (N : ℝ) ^ (2 * (max κ 0 + 1)) := by
    rw [hT, ← Real.rpow_add hNpos]; congr 1; ring
  have hexp : (N : ℝ) ^ (1 / 2 + w - s.re) * (N : ℝ) ^ (2 * (max κ 0 + 1)) ≤ (N : ℝ) ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hinv : (N : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.rpow_neg_one]
    rw [inv_le_comm₀ hNpos (by norm_num)]
    norm_num
    exact_mod_cast hN2
  have h0 : 0 ≤ (N : ℝ) ^ (1 / 2 + w - s.re) := (Real.rpow_pos_of_pos hNpos _).le
  calc (N : ℝ) ^ (1 / 2 + w - s.re) * max 1 (‖lx‖ + ‖(N : ℂ) * ox‖) * max 1 (‖ly‖ + ‖(N : ℂ) * oy‖)
      ≤ (N : ℝ) ^ (1 / 2 + w - s.re) * (2 * T) * (2 * T) := by gcongr
    _ = 4 * ((N : ℝ) ^ (1 / 2 + w - s.re) * (N : ℝ) ^ (2 * (max κ 0 + 1))) := by rw [← hTT]; ring
    _ ≤ 4 * (1 / 2) := by gcongr; exact hexp.trans hinv
    _ < (N : ℝ) ^ 2 := by nlinarith

end LocalFactor

section Analytic

open Filter Topology

theorem hasProd_of_hasProd_inv {ι : Type*} (f : ι → ℂ) {a : ℂ} (ha : a ≠ 0)
    (h : HasProd (fun i => (f i)⁻¹) a) : HasProd f a⁻¹ := by
  unfold HasProd at h ⊢
  have h' := h.inv₀ ha
  refine h'.congr (fun T => ?_)
  simp [Finset.prod_inv_distrib]

theorem ne_zero_of_tprod_ne_zero {ι : Type*} {f : ι → ℂ} (hf : Multipliable f) (h : ∏' i, f i ≠ 0) (i : ι) :
    f i ≠ 0 := by
  intro hi
  apply h
  have hp := hf.hasProd
  have h0 : Tendsto (fun L : Finset ι => ∏ j ∈ L, f j) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop {i}] with L hL
    exact (Finset.prod_eq_zero (hL (Finset.mem_singleton_self i)) hi).symm
  exact tendsto_nhds_unique hp h0

theorem countable_heightOneSpectrum (K : Type) [Field K] [NumberField K] :
    Countable (HeightOneSpectrum (𝓞 K)) := by
  have hI : Set.Countable (Set.univ : Set (Ideal (𝓞 K))) := by
    have : (Set.univ : Set (Ideal (𝓞 K))) = ⋃ n : ℕ, {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := by
      ext I; simp
    rw [this]
    exact Set.countable_iUnion (fun n => (Ideal.finite_setOf_absNorm_eq n).countable)
  haveI : Countable (Ideal (𝓞 K)) := Set.countable_univ_iff.mp hI
  exact (Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
    (fun v w h => HeightOneSpectrum.ext h))

end Analytic

section PlaceFacts

variable (K : Type) [Field K] [NumberField K]

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

open LanglandsTunnell.RankinSelberg Polynomial in

theorem eval_point_eq (N : ℕ) (hN : 0 < N) (w : ℝ) (s m : ℂ) :
    (m * (N : ℂ) ^ ((1 / 2 + w : ℂ) - s)) / (N : ℂ) ^ 2 = m * (N : ℂ) ^ (-(s + ((3 / 2 - w : ℝ) : ℂ))) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [mul_div_assoc, ← Complex.cpow_two, ← Complex.cpow_sub _ _ hN0]
  congr 2
  push_cast
  ring

theorem num_point_eq (N : ℕ) (hN : 0 < N) (w c : ℝ) (s m : ℂ) :
    ((m * (N : ℂ) ^ ((1 / 2 + w : ℂ) - s)) / (N : ℂ)) ^ 2 =
      (m ^ 2 * (N : ℂ) ^ ((-(2 * c) : ℝ) : ℂ)) * (N : ℂ) ^ (-(2 * s + ((1 - 2 * w - 2 * c : ℝ) : ℂ))) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [div_pow, mul_pow, ← Complex.cpow_nat_mul, show ((N : ℂ)) ^ 2 = (N : ℂ) ^ (2 : ℂ) from (Complex.cpow_two _).symm,
    mul_div_assoc, ← Complex.cpow_sub _ _ hN0, mul_assoc, ← Complex.cpow_add _ _ hN0]
  congr 2
  push_cast
  ring

end PlaceFacts

section Main

open Filter Topology LanglandsTunnell.RankinSelberg UnramifiedWhittaker Polynomial
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem main (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
      (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
      (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (_hψ : IsGlobalAddChar K ψ)
      (μ ν ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hZ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))
      (_hμF : IsIdeleClassChar (𝓞 K) K μ) (_hνF : IsIdeleClassChar (𝓞 K) K ν)
      (x y : AdelicGL2 (𝓞 K) K → ℂ)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        y (globalPoints (𝓞 K) K γ * g) = y g)
      (_hxc : Continuous x) (_hyc : Continuous y)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
      (_hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (_hxK : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          x (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = x g)
      (_hyK : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          y (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = y g)
      (lx ox ly oy : HeightOneSpectrum (𝓞 K) → ℂ) (κ : ℝ)
      (_hbd : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ‖lx v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖ox v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖ly v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖oy v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
      (_hP : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ,
          whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 ((heckeGen (𝓞 K) K v) ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1
              ((heckeGen (𝓞 K) K v) ^ m * g)) =
          heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lx v) (ox v) m *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (ly v) (oy v) m *
            (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 g *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1 g)))
      (_hPneg : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ, 0 < m →
          whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1
              ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g)) = 0),
    ∃ σ₀ : ℝ, ∀ (s : ℂ), σ₀ < s.re →
      ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ → Continuous φ →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
          ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
            φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g) →
        ∀ (d₁ d₂ : ℝ), Integrable (fun q : RationalCentreUnipotentQuotient K =>
            RankinSelberg.quotientIntegrand K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ q.out)
          (rationalCentreUnipotentQuotientMeasure K) →
        ∃ Prod : ℂ,
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
            (1 - ox v.1 * oy v.1 *
                ((((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
                    ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 / 2 + w : ℂ) - s)) /
                  ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ)) ^ 2) /
              (LanglandsTunnell.RankinSelberg.rsEulerPoly (lx v.1) (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) * ox v.1)
                  (ly v.1) (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) * oy v.1) 0).eval
                ((((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
                    ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 / 2 + w : ℂ) - s)) /
                  ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ 2)) Prod ∧
          RankinSelberg.quotientIntegral K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ =
            RankinSelberg.sPartIntegral K S (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ * Prod := by
  intro α hα D U gen ψ hψ μ ν ωx ωy w hμ hν hZ hμF hνF x y hxG hyG hxc hyc hxZ hyZ S hxK hyK lx ox ly oy κ hbd
    hP hPneg
  have hαn : ∀ t, ((α t : ℝˣ) : ℝ) = ideleNorm K t := fun t => rfl

  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := (isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant K).1
  haveI := (isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant K).2
  haveI : Countable (HeightOneSpectrum (𝓞 K)) := countable_heightOneSpectrum K

  obtain ⟨sec, -, hsec, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq K
  set Nn : HeightOneSpectrum (𝓞 K) → ℕ := fun v => Ideal.absNorm v.asIdeal with hNn
  have hN2 : ∀ v, 2 ≤ Nn v := fun v => two_le_absNorm K v
  have hNpos : ∀ v, 0 < Nn v := fun v => lt_of_lt_of_le (by norm_num) (hN2 v)
  have hN1r : ∀ v, (1 : ℝ) ≤ (Nn v : ℝ) := fun v => by exact_mod_cast (hNpos v)
  set mv : HeightOneSpectrum (𝓞 K) → ℂ := fun v => ((μ (uniformizerIdele K v) : ℂˣ) : ℂ) with hmv
  have hmv1 : ∀ v, ‖mv v‖ = 1 := fun v => hμ _
  set κp : ℝ := max κ 0 with hκp
  have hκp0 : 0 ≤ κp := le_max_right κ 0
  have hbd' : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      ‖lx v.1‖ ≤ (Nn v.1 : ℝ) ^ κp ∧ ‖ox v.1‖ ≤ (Nn v.1 : ℝ) ^ κp ∧
        ‖ly v.1‖ ≤ (Nn v.1 : ℝ) ^ κp ∧ ‖oy v.1‖ ≤ (Nn v.1 : ℝ) ^ κp := by
    intro v
    have h := hbd v.1 v.2
    have hle : (Nn v.1 : ℝ) ^ κ ≤ (Nn v.1 : ℝ) ^ κp :=
      Real.rpow_le_rpow_of_exponent_le (hN1r v.1) (le_max_left κ 0)
    exact ⟨h.1.trans hle, h.2.1.trans hle, h.2.2.1.trans hle, h.2.2.2.trans hle⟩

  obtain ⟨σA, hA1, -, hA3⟩ :=
    LanglandsTunnell.RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow K S
      (fun v => mv v.1 * lx v.1) (fun v => mv v.1 ^ 2 * ((Nn v.1 : ℂ) * ox v.1)) (fun v => ly v.1)
      (fun v => (Nn v.1 : ℂ) * oy v.1) (κp + 1) (by
        intro v
        obtain ⟨h1, h2, h3, h4⟩ := hbd' v
        have hNv : (0 : ℝ) < Nn v.1 := by exact_mod_cast hNpos v.1
        have hup : (Nn v.1 : ℝ) ^ κp ≤ (Nn v.1 : ℝ) ^ (κp + 1) :=
          Real.rpow_le_rpow_of_exponent_le (hN1r v.1) (by linarith)
        have hup' : (Nn v.1 : ℝ) * (Nn v.1 : ℝ) ^ κp = (Nn v.1 : ℝ) ^ (κp + 1) := by
          rw [Real.rpow_add_one hNv.ne', mul_comm]
        refine ⟨?_, ?_, h3.trans hup, ?_⟩
        · rw [norm_mul, hmv1, one_mul]; exact h1.trans hup
        · rw [norm_mul, norm_pow, hmv1, one_pow, one_mul, norm_mul, Complex.norm_natCast, ← hup']
          exact mul_le_mul_of_nonneg_left h2 hNv.le
        · rw [norm_mul, Complex.norm_natCast, ← hup']
          exact mul_le_mul_of_nonneg_left h4 hNv.le)
  refine ⟨max (w + 2 * κp + 7 / 2) (max (σA + w - 3 / 2) (w + κp)) + 1, ?_⟩
  intro s hs φ hφ hφc hφK d₁ d₂ hint
  have hs1 : w + 2 * κp + 7 / 2 < s.re := by
    linarith [le_max_left (w + 2 * κp + 7 / 2) (max (σA + w - 3 / 2) (w + κp))]
  have hs2 : σA < (s + ((3 / 2 - w : ℝ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [le_max_right (w + 2 * κp + 7 / 2) (max (σA + w - 3 / 2) (w + κp)),
      le_max_left (σA + w - 3 / 2) (w + κp)]
  have hs3 : 1 < (2 * s + ((1 - 2 * w - 2 * κp : ℝ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
      sub_zero]
    linarith [le_max_right (w + 2 * κp + 7 / 2) (max (σA + w - 3 / 2) (w + κp)),
      le_max_right (σA + w - 3 / 2) (w + κp)]

  set pins := productionPinsOf K D U gen (adelicBox K) with hpins
  set Hf := RankinSelberg.quotientIntegrand K pins ψ x y φ w d₁ d₂ with hHf

  have hrt : ∀ v : HeightOneSpectrum (𝓞 K), NNReal.sqrt (Nn v : ℝ≥0) ≠ 0 := fun v => by
    rw [Ne, NNReal.sqrt_eq_zero]; exact_mod_cast (hNpos v).ne'
  set u : HeightOneSpectrum (𝓞 K) → (AdeleRing (𝓞 K) K)ˣ := fun v => sec (Units.mk0 (NNReal.sqrt (Nn v : ℝ≥0)) (hrt v))
    with hu_def
  have hu : ∀ v, ideleNorm K (u v) = Real.sqrt (Nn v : ℝ) := by
    intro v
    rw [hu_def, hsec]
    simp
  set b : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → AdelicGL2 (𝓞 K) K :=
    fun v => heckeGen (𝓞 K) K v.1 * centralScalar (𝓞 K) K (u v.1) with hb_def
  set Cv : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ := fun v =>
    ((((Real.sqrt (Nn v.1 : ℝ)) ^ (2 * w) : ℝ) : ℂ) * (mv v.1 * ((((Nn v.1 : ℝ))⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2)))
    with hCv
  set Φ : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℤ → ℂ := fun v =>
    shellWeight (Cv v) (heckeRecursionSeq (Nn v.1) (lx v.1) (ox v.1)) (heckeRecursionSeq (Nn v.1) (ly v.1) (oy v.1))
    with hΦ
  set m : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → AdelicGL2 (𝓞 K) K → ℤ := fun v => iwasawaShellIndex K v.1
    with hm_def
  set Dv : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℝ≥0 := fun v => (Nn v.1 : ℝ≥0) with hDv
  set f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ := fun v =>
    (1 - ox v.1 * oy v.1 * ((mv v.1 * (Nn v.1 : ℂ) ^ ((1 / 2 + w : ℂ) - s)) / (Nn v.1 : ℂ)) ^ 2) /
      (rsEulerPoly (lx v.1) ((Nn v.1 : ℂ) * ox v.1) (ly v.1) ((Nn v.1 : ℂ) * oy v.1) 0).eval
        ((mv v.1 * (Nn v.1 : ℂ) ^ ((1 / 2 + w : ℂ) - s)) / (Nn v.1 : ℂ) ^ 2) with hf

  have hb : ∀ (i : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (y' : AdelicGL2 (𝓞 K) K),
      y' ∈ rationalCentreUnipotent K ↔ b i * y' * (b i)⁻¹ ∈ rationalCentreUnipotent K :=
    fun i y' => mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem K i.1 (u i.1) y'
  have hD0 : ∀ i : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, Dv i ≠ 0 := fun i => by
    have : Dv i = (Nn i.1 : ℝ≥0) := rfl
    rw [this]; exact_mod_cast (hNpos i.1).ne'
  have hbD : ∀ (i : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (F : rationalCentreUnipotent K → ℝ≥0∞), Measurable F →
      ∫⁻ x', F ⟨b i * (x' : AdelicGL2 (𝓞 K) K) * (b i)⁻¹, (hb i (x' : AdelicGL2 (𝓞 K) K)).mp x'.2⟩
          ∂(rationalCentreUnipotentHaar K) =
        (Dv i : ℝ≥0∞) * ∫⁻ x', F x' ∂(rationalCentreUnipotentHaar K) := by
    intro i F hF
    have h := lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj K i.1 (u i.1) (hb i) F hF
    rw [h, hDv, ENNReal.coe_natCast]
  have hm : ∀ i : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, Measurable (m i) :=
    fun i => (isLocallyConstant_iwasawaShellIndex_and_measurable K i.1).2
  have hmH : ∀ (i : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}), ∀ x' ∈ rationalCentreUnipotent K,
      ∀ g : AdelicGL2 (𝓞 K) K, m i (x' * g) = m i g :=
    fun i x' hx' g => iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent K i.1 x' hx' g
  have hmb : ∀ (i : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (g : AdelicGL2 (𝓞 K) K), m i (b i * g) = m i g + 1 := by
    intro i g
    simp only [hm_def, hb_def, mul_assoc]
    rw [iwasawaShellIndex_heckeGen_mul, iwasawaShellIndex_centralScalar_mul]
  have hmb' : ∀ (i j : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}), i ≠ j →
      ∀ g : AdelicGL2 (𝓞 K) K, m i (b j * g) = m i g := by
    intro i j hij g
    have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    simp only [hm_def, hb_def, mul_assoc]
    rw [iwasawaShellIndex_heckeGen_mul_of_ne _ _ hij', iwasawaShellIndex_centralScalar_mul]
  have hHm : Measurable Hf := measurable_quotientIntegrand K D U gen ψ hψ.continuous x y φ hxc hyc hφc w d₁ d₂
  have hHH : ∀ x' ∈ rationalCentreUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, Hf (x' * g) = Hf g :=
    quotientIntegrand_mul_of_mem_rationalCentreUnipotent K D U gen ψ hψ μ ν α hα s hμF hνF x y φ hxG hyG hφ w d₁ d₂
  have hrel : ∀ (i : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (g : AdelicGL2 (𝓞 K) K), m i g = 0 →
      ∀ n : ℤ, Hf (b i ^ n * g) = Φ i n * Hf g := by
    intro i g hg n
    exact quotientIntegrand_shift_zpow_mul K pins ψ μ ν ωx ωy α hα hαn w hZ s x y φ hxZ hyZ hφ d₁ d₂ i.1
      (heckeRecursionSeq (Nn i.1) (lx i.1) (ox i.1)) (heckeRecursionSeq (Nn i.1) (ly i.1) (oy i.1))
      (fun g' hg' k => hP i.1 i.2 g' ((iwasawaShellIndex_eq_zero_iff' i.1 g').mp hg') k)
      (fun g' hg' k hk => hPneg i.1 i.2 g' ((iwasawaShellIndex_eq_zero_iff' i.1 g').mp hg') k hk)
      (u i.1) (hu i.1) (ideleNorm_uniformizerIdele K i.1) (hNpos i.1).ne' g hg n

  have hden_eq : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      (rsEulerPoly (lx v.1) ((Nn v.1 : ℂ) * ox v.1) (ly v.1) ((Nn v.1 : ℂ) * oy v.1) 0).eval
          ((mv v.1 * (Nn v.1 : ℂ) ^ ((1 / 2 + w : ℂ) - s)) / (Nn v.1 : ℂ) ^ 2) =
        (rsEulerPoly (mv v.1 * lx v.1) (mv v.1 ^ 2 * ((Nn v.1 : ℂ) * ox v.1)) (ly v.1) ((Nn v.1 : ℂ) * oy v.1) 0).eval
          ((Nn v.1 : ℂ) ^ (-(s + ((3 / 2 - w : ℝ) : ℂ)))) := by
    intro v
    rw [eval_point_eq _ (hNpos v.1), eval_rsEulerPoly_scale]
  have hdenM := hA1 (s + ((3 / 2 - w : ℝ) : ℂ)) hs2
  have hdenP := hA3 (s + ((3 / 2 - w : ℝ) : ℂ)) hs2
  have hden_ne : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      (rsEulerPoly (lx v.1) ((Nn v.1 : ℂ) * ox v.1) (ly v.1) ((Nn v.1 : ℂ) * oy v.1) 0).eval
          ((mv v.1 * (Nn v.1 : ℂ) ^ ((1 / 2 + w : ℂ) - s)) / (Nn v.1 : ℂ) ^ 2) ≠ 0 := by
    intro v he
    have h := ne_zero_of_tprod_ne_zero hdenM hdenP v
    apply h
    rw [← hden_eq v, he, inv_zero]

  have hloc : ∀ i : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      Summable (fun n : ℤ => (Dv i : ℝ) ^ n * ‖Φ i n‖) ∧ ∑' n : ℤ, ((Dv i : ℝ) : ℂ) ^ n * Φ i n = f i := by
    intro i
    have hsum := summable_heckeSeries_of_lt_re (Nn i.1) (hN2 i.1) κ w s (lx i.1) (ox i.1) (ly i.1) (oy i.1)
      (mv i.1) (hmv1 i.1) (hbd i.1 i.2) hs1
    obtain ⟨h1, h2⟩ := tsum_shellWeight_eq_localFactor (Nn i.1) (hNpos i.1) w s (mv i.1) (lx i.1) (ox i.1)
      (ly i.1) (oy i.1) hsum (hden_ne i)
    have hD : ((Dv i : ℝ)) = (Nn i.1 : ℝ) := by rw [hDv]; exact NNReal.coe_natCast _
    refine ⟨?_, ?_⟩
    · rw [hD]; exact h1
    · rw [hD]; exact h2

  set z : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ := fun v =>
    ox v.1 * oy v.1 * (mv v.1 ^ 2 * (Nn v.1 : ℂ) ^ (((-(2 * κp)) : ℝ) : ℂ)) with hz
  have hz1 : ∀ v, ‖z v‖ ≤ 1 := by
    intro v
    obtain ⟨-, h2, -, h4⟩ := hbd' v
    have hNv : 0 < (Nn v.1 : ℝ) := by exact_mod_cast hNpos v.1
    rw [hz]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, hmv1, one_pow, one_mul,
      Complex.norm_natCast_cpow_of_pos (hNpos v.1), Complex.ofReal_re]
    have hone : (Nn v.1 : ℝ) ^ κp * (Nn v.1 : ℝ) ^ κp * (Nn v.1 : ℝ) ^ (-(2 * κp)) = 1 := by
      rw [← Real.rpow_add hNv, ← Real.rpow_add hNv]
      have : κp + κp + -(2 * κp) = 0 := by ring
      rw [this, Real.rpow_zero]
    calc ‖ox v.1‖ * ‖oy v.1‖ * (Nn v.1 : ℝ) ^ (-(2 * κp))
        ≤ (Nn v.1 : ℝ) ^ κp * (Nn v.1 : ℝ) ^ κp * (Nn v.1 : ℝ) ^ (-(2 * κp)) := by
          gcongr
      _ = 1 := hone
  obtain ⟨hB1, -, hB3⟩ := NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K S z hz1
  have hnumM := hB1 (2 * s + ((1 - 2 * w - 2 * κp : ℝ) : ℂ)) hs3
  have hnumP := hB3 (2 * s + ((1 - 2 * w - 2 * κp : ℝ) : ℂ)) hs3
  have hnum_eq : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      1 - ox v.1 * oy v.1 * ((mv v.1 * (Nn v.1 : ℂ) ^ ((1 / 2 + w : ℂ) - s)) / (Nn v.1 : ℂ)) ^ 2 =
        1 - z v * (Nn v.1 : ℂ) ^ (-(2 * s + ((1 - 2 * w - 2 * κp : ℝ) : ℂ))) := by
    intro v
    rw [num_point_eq _ (hNpos v.1) w κp s (mv v.1), hz]
    ring

  have hfeq : f = fun v => (1 - z v * (Nn v.1 : ℂ) ^ (-(2 * s + ((1 - 2 * w - 2 * κp : ℝ) : ℂ)))) *
      ((rsEulerPoly (mv v.1 * lx v.1) (mv v.1 ^ 2 * ((Nn v.1 : ℂ) * ox v.1)) (ly v.1) ((Nn v.1 : ℂ) * oy v.1) 0).eval
          ((Nn v.1 : ℂ) ^ (-(s + ((3 / 2 - w : ℝ) : ℂ)))))⁻¹ := by
    funext v
    rw [hf]
    beta_reduce
    rw [div_eq_mul_inv, hnum_eq, hden_eq]
  have hprod : HasProd f
      ((∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          (1 - z v * (Nn v.1 : ℂ) ^ (-(2 * s + ((1 - 2 * w - 2 * κp : ℝ) : ℂ))))⁻¹)⁻¹ *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          ((rsEulerPoly (mv v.1 * lx v.1) (mv v.1 ^ 2 * ((Nn v.1 : ℂ) * ox v.1)) (ly v.1) ((Nn v.1 : ℂ) * oy v.1)
              0).eval ((Nn v.1 : ℂ) ^ (-(s + ((3 / 2 - w : ℝ) : ℂ)))))⁻¹) := by
    rw [hfeq]
    exact (hasProd_of_hasProd_inv
      (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        1 - z v * (Nn v.1 : ℂ) ^ (-(2 * s + ((1 - 2 * w - 2 * κp : ℝ) : ℂ)))) hnumP hnumM.hasProd).mul
      hdenM.hasProd

  have hν : rationalCentreUnipotentQuotientMeasure K =
      HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalCentreUnipotent K) (rationalCentreUnipotentHaar K) :=
    rfl
  have hint' : Integrable (fun q : RationalCentreUnipotentQuotient K => Hf q.out)
      (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalCentreUnipotent K)
        (rationalCentreUnipotentHaar K)) := by
    rw [← hν]; exact hint
  have hpeel : ∀ L : Finset {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      (∫ q, Hf q.out ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalCentreUnipotent K)
        (rationalCentreUnipotentHaar K))) =
      (∏ i ∈ L, ∑' n : ℤ, ((Dv i : ℝ) : ℂ) ^ n * Φ i n) *
        ∫ q in {q : RationalCentreUnipotentQuotient K | ∀ i ∈ L, m i q.out = 0}, Hf q.out
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalCentreUnipotent K)
            (rationalCentreUnipotentHaar K)) :=
    fun L => peel_finset (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalCentreUnipotent K)
      (isClosed_rationalCentreUnipotent K) (rationalCentreUnipotentHaar K) b hb Dv hD0 hbD m hm hmH hmb hmb'
      Hf hHm hHH Φ (fun i => (hloc i).1) hrel hint' L
  have hI : ∀ L : Finset {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      RankinSelberg.quotientIntegral K pins ψ x y φ w d₁ d₂ =
        (∏ i ∈ L, f i) *
          ∫ q in {q : RationalCentreUnipotentQuotient K | ∀ i ∈ L, m i q.out = 0}, Hf q.out
            ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalCentreUnipotent K)
              (rationalCentreUnipotentHaar K)) := by
    intro L
    have h := hpeel L
    rw [Finset.prod_congr rfl (fun i _ => (hloc i).2)] at h
    exact h
  have hT := tendsto_setIntegral_shells
    (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalCentreUnipotent K) (rationalCentreUnipotentHaar K))
    m hm hmH Hf hint'
  have hSset : {q : RationalCentreUnipotentQuotient K | ∀ i : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, m i q.out = 0} =
      {q | q.out ∈ RankinSelberg.shellZeroOutside K S} := by
    ext q
    simp only [Set.mem_setOf_eq, RankinSelberg.shellZeroOutside, hm_def, Subtype.forall, iwasawaShellIndex_eq_zero_iff']
  rw [hSset] at hT
  have hlim : Tendsto (fun L : Finset {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      (∏ i ∈ L, f i) *
        ∫ q in {q : RationalCentreUnipotentQuotient K | ∀ i ∈ L, m i q.out = 0}, Hf q.out
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalCentreUnipotent K)
            (rationalCentreUnipotentHaar K))) atTop
      (𝓝 (((∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          (1 - z v * (Nn v.1 : ℂ) ^ (-(2 * s + ((1 - 2 * w - 2 * κp : ℝ) : ℂ))))⁻¹)⁻¹ *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          ((rsEulerPoly (mv v.1 * lx v.1) (mv v.1 ^ 2 * ((Nn v.1 : ℂ) * ox v.1)) (ly v.1) ((Nn v.1 : ℂ) * oy v.1)
              0).eval ((Nn v.1 : ℂ) ^ (-(s + ((3 / 2 - w : ℝ) : ℂ)))))⁻¹) *
        RankinSelberg.sPartIntegral K S pins ψ x y φ w d₁ d₂)) :=
    Filter.Tendsto.mul hprod hT
  have hconst := hlim.congr (fun L => (hI L).symm)
  have heq := tendsto_nhds_unique tendsto_const_nhds hconst
  refine ⟨_, hprod, ?_⟩
  rw [heq, mul_comm]

end Main

end EulerUnfold
p2m_reactivate "P2MW.S_AutomorphicForm_RankinSelberg_exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion.EulerUnfold"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm IsDedekindDomain UnramifiedWhittaker
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
      (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
      (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (_hψ : IsGlobalAddChar K ψ)
      (μ ν ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hZ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))
      (_hμF : IsIdeleClassChar (𝓞 K) K μ) (_hνF : IsIdeleClassChar (𝓞 K) K ν)
      (x y : AdelicGL2 (𝓞 K) K → ℂ)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        y (globalPoints (𝓞 K) K γ * g) = y g)
      (_hxc : Continuous x) (_hyc : Continuous y)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
      (_hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (_hxK : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          x (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = x g)
      (_hyK : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          y (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = y g)
      (lx ox ly oy : HeightOneSpectrum (𝓞 K) → ℂ) (κ : ℝ)
      (_hbd : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ‖lx v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖ox v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖ly v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖oy v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
      (_hP : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ,
          whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 ((heckeGen (𝓞 K) K v) ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1
              ((heckeGen (𝓞 K) K v) ^ m * g)) =
          heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lx v) (ox v) m *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (ly v) (oy v) m *
            (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 g *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1 g)))
      (_hPneg : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ, 0 < m →
          whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1
              ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g)) = 0),
    ∃ σ₀ : ℝ, ∀ (s : ℂ), σ₀ < s.re →
      ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ → Continuous φ →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
          ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
            φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g) →
        ∀ (d₁ d₂ : ℝ), Integrable (fun q : RationalCentreUnipotentQuotient K =>
            RankinSelberg.quotientIntegrand K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ q.out)
          (rationalCentreUnipotentQuotientMeasure K) →
        ∃ Prod : ℂ,
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
            (1 - ox v.1 * oy v.1 *
                ((((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
                    ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 / 2 + w : ℂ) - s)) /
                  ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ)) ^ 2) /
              (LanglandsTunnell.RankinSelberg.rsEulerPoly (lx v.1) (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) * ox v.1)
                  (ly v.1) (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) * oy v.1) 0).eval
                ((((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
                    ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 / 2 + w : ℂ) - s)) /
                  ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ 2)) Prod ∧
          RankinSelberg.quotientIntegral K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ =
            RankinSelberg.sPartIntegral K S (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ * Prod :=
  EulerUnfold.main K

end S_AutomorphicForm_RankinSelberg_exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion
end P2MW
export P2MW.S_AutomorphicForm_RankinSelberg_exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion (solution)
