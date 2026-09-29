-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/64dc82a8-e74f-536a-a298-fdcede7065f2

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds
import Theorems.Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_AutomorphicForm_isCuspidalFn_rightConv
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.adeleBorel

open scoped Topology ProbabilityTheory

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (μ : ℂ) (hμ : μ ≠ 0) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : Tc v = μ • v) :
    ∃ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ cuspMemberSubmodule F Φ₀ ξ),
      toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ = v ∧ rightConv F ψ f = μ • ψ := by
  classical
  haveI hBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI hHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI hHc : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier; exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set μH : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμH
  obtain ⟨hfc, hfsupp⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf

  have hmc : ∀ θ : AdelicGL2 (𝓞 F) F → ℂ, θ ∈ cuspMemberSubmodule F Φ₀ ξ → rightConv F θ f ∈ cuspMemberSubmodule F Φ₀ ξ :=
    fun θ hθ => AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hf θ hθ
  have hdense : Dense (Set.range (toCuspSubcarrier F hΦ₀ σ ξ) : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
    rw [Subtype.dense_iff]
    intro z hz
    have hz' : z ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) : Set (Carrier F Φ₀ σ))) := by
      rw [← Submodule.topologicalClosure_coe]; exact hz
    refine closure_mono ?_ hz'
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩, ⟨⟨ψ, hψ⟩, rfl⟩, rfl⟩
  obtain ⟨w, hw_mem, hw_lim⟩ := mem_closure_iff_seq_limit.mp (hdense v)
  choose φm hφm using fun n => Set.mem_range.mp (hw_mem n)

  set φ : ℕ → (AdelicGL2 (𝓞 F) F → ℂ) := fun n => ((φm n : ↥(cuspMemberSubmodule F Φ₀ ξ)) : AdelicGL2 (𝓞 F) F → ℂ) with hφdef
  have hφmem : ∀ n, φ n ∈ cuspMemberSubmodule F Φ₀ ξ := fun n => (φm n).2
  have hφw : ∀ n, toCuspSubcarrier F hΦ₀ σ ξ ⟨φ n, hφmem n⟩ = w n := fun n => hφm n
  have hTφ : ∀ n, Tc (w n) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F (φ n) f, hmc _ (hφmem n)⟩ := fun n => by
    rw [← hφw n]; exact hcomm ⟨φ n, hφmem n⟩ (hmc _ (hφmem n))
  have hTlim : Filter.Tendsto (fun n => toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F (φ n) f, hmc _ (hφmem n)⟩)
      Filter.atTop (𝓝 (μ • v)) := by
    have h := (Tc.continuous.tendsto v).comp hw_lim
    rw [hv] at h
    refine h.congr fun n => ?_
    exact hTφ n

  have hint : ∀ θ : AdelicGL2 (𝓞 F) F → ℂ, Continuous θ → ∀ x, Integrable (fun y => θ (x * y) * f y) μH := fun θ hθ x =>
    ((hθ.comp (continuous_const.mul continuous_id)).mul hfc).integrable_of_hasCompactSupport hfsupp.mul_left
  have hconv_sub : ∀ θ₁ θ₂ : AdelicGL2 (𝓞 F) F → ℂ, Continuous θ₁ → Continuous θ₂ →
      rightConv F (θ₁ - θ₂) f = rightConv F θ₁ f - rightConv F θ₂ f := by
    intro θ₁ θ₂ h₁ h₂
    funext x
    simp only [rightConv_apply, Pi.sub_apply]
    rw [← hμH, ← integral_sub (hint θ₁ h₁ x) (hint θ₂ h₂ x)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring

  set m : ℝ := min (α ^ (-σ)) (β ^ (-σ)) with hm
  have hm0 : 0 < m := lt_min (Real.rpow_pos_of_pos hΦ₀.pos _) (Real.rpow_pos_of_pos hΦ₀.pos_right _)
  have hm' : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.mpr hm0).ne'
  have hwm : ∀ x ∈ Φ₀, m ≤ weight F σ x := by
    intro x hx
    rw [weight_def]
    obtain ⟨hα, hβ⟩ := (mem_detNormSlab F α β x).mp (hΦ₀.subset hx)
    rcases le_or_gt 0 σ with hσ0 | hσ0
    · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (hΦ₀.pos.trans_le hα) hβ (neg_nonpos.mpr hσ0))
    · exact (min_le_left _ _).trans (Real.rpow_le_rpow hΦ₀.pos.le hα (neg_nonneg.mpr hσ0.le))

  have hres0 : (μH.restrict (detNormSlab F α β)).restrict Φ₀ = μH.restrict Φ₀ := by
    rw [Measure.restrict_restrict₀ hΦ₀.isFundamentalDomain.nullMeasurableSet, Set.inter_eq_left.mpr hΦ₀.subset]
  have hae : ∀ᵐ x ∂(μH.restrict Φ₀), x ∈ Φ₀ := by
    rw [← hres0]; exact ae_restrict_mem₀ hΦ₀.isFundamentalDomain.nullMeasurableSet

  have hle : μH.restrict Φ₀ ≤ (ENNReal.ofReal m)⁻¹ • weightedMeasure F Φ₀ σ := by
    rw [Measure.le_iff]
    intro t ht
    unfold weightedMeasure
    rw [Measure.smul_apply, withDensity_apply _ ht, smul_eq_mul, ← hμH]
    have hlow : ENNReal.ofReal m * (μH.restrict Φ₀) t ≤ ∫⁻ x in t, ENNReal.ofReal (weight F σ x) ∂(μH.restrict Φ₀) := by
      rw [← setLIntegral_const]
      refine lintegral_mono_ae ((ae_restrict_of_ae hae).mono fun x hx => ?_)
      exact ENNReal.ofReal_le_ofReal (hwm x hx)
    have hm' : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.mpr hm0).ne'
    calc (μH.restrict Φ₀) t = (ENNReal.ofReal m)⁻¹ * (ENNReal.ofReal m * (μH.restrict Φ₀) t) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hm' ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal m)⁻¹ * ∫⁻ x in t, ENNReal.ofReal (weight F σ x) ∂(μH.restrict Φ₀) := mul_le_mul_right hlow _
  have hKcmp : ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (θ : AdelicGL2 (𝓞 F) F → ℂ) (hθ : θ ∈ memberSubmodule F Φ₀ ξ),
      (eLpNorm θ 2 (μH.restrict Φ₀)).toReal ≤ Kc * ‖toCarrier F hΦ₀ σ ξ ⟨θ, hθ⟩‖ := by
    refine ⟨(((ENNReal.ofReal m)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal, ENNReal.toReal_nonneg, fun θ hθ => ?_⟩
    have h1 := eLpNorm_mono_measure θ hle (p := 2)
    rw [eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)] at h1
    have hnorm : ‖toCarrier F hΦ₀ σ ξ ⟨θ, hθ⟩‖ = (eLpNorm θ 2 (weightedMeasure F Φ₀ σ)).toReal :=
      MeasureTheory.Lp.norm_toLp θ (memLp_weightedMeasure_of_mem F hΦ₀ σ hθ)
    rw [hnorm, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono ?_ h1
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (ENNReal.inv_ne_top.mpr
      (ENNReal.ofReal_pos.mpr hm0).ne')) (memLp_weightedMeasure_of_mem F hΦ₀ σ hθ).eLpNorm_ne_top
  obtain ⟨Kc, hKc0, hKc⟩ := hKcmp

  have hwin : ∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c → 0 < d₁ → ∃ C : ℝ, ∀ n m,
      ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂),
        ‖rightConv F (φ n) f g - rightConv F (φ m) f g‖ ≤ C * ‖w n - w m‖ := by
    intro c u d₁ d₂ T hc hd₁
    obtain ⟨C, hC⟩ := AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
      F ξ f hf c u d₁ d₂ T hc hd₁ α β hΦ₀.pos_right hΦ₀.lt Φ₀ hΦ₀.isFundamentalDomain
    refine ⟨max C 0 * Kc, fun n m g hg => ?_⟩
    have hθ : φ n - φ m ∈ cuspMemberSubmodule F Φ₀ ξ := Submodule.sub_mem _ (hφmem n) (hφmem m)
    obtain ⟨hlx, h2⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ (φ n - φ m)).mp hθ.1.1.1
    have hb := hC (φ n - φ m) hlx hθ.1.1.2 hθ.2 h2 g hg
    rw [hconv_sub (φ n) (φ m) (hφmem n).2 (hφmem m).2, Pi.sub_apply] at hb
    replace hb := hb.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) ENNReal.toReal_nonneg)
    have hcar : ‖toCarrier F hΦ₀ σ ξ ⟨φ n - φ m, hθ.1.1.1⟩‖ = ‖w n - w m‖ := by
      rw [← hφw n, ← hφw m, ← map_sub, Submodule.coe_norm, toCuspSubcarrier_apply_coe]
      rfl
    refine hb.trans ?_
    calc max C 0 * (eLpNorm (φ n - φ m) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)).toReal
        ≤ max C 0 * (Kc * ‖toCarrier F hΦ₀ σ ξ ⟨φ n - φ m, hθ.1.1.1⟩‖) :=
          mul_le_mul_of_nonneg_left (hKc _ _) (le_max_right C 0)
      _ = max C 0 * Kc * ‖w n - w m‖ := by rw [hcar, mul_assoc]

  have hwC : CauchySeq w := hw_lim.cauchySeq
  have hpt : ∀ g : AdelicGL2 (𝓞 F) F, ∃ L : ℂ, Filter.Tendsto (fun n => rightConv F (φ n) f g) Filter.atTop (𝓝 L) := by
    intro g
    obtain ⟨c, u, d₁, d₂, T, hc, hd₁, hWg⟩ := AutomorphicForm.exists_iUnion_centreCutSiegelSet_mem_nhds F g
    obtain ⟨C, hC⟩ := hwin c u d₁ d₂ T hc hd₁
    have hgW := mem_of_mem_nhds hWg
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.mpr fun ε hε => ?_)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hwC (ε / (|C| + 1)) (by positivity)
    refine ⟨N, fun n hn m hm => ?_⟩
    rw [dist_eq_norm]
    calc ‖rightConv F (φ n) f g - rightConv F (φ m) f g‖ ≤ C * ‖w n - w m‖ := hC n m g hgW
      _ ≤ (|C| + 1) * ‖w n - w m‖ := mul_le_mul_of_nonneg_right ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one)) (norm_nonneg _)
      _ < (|C| + 1) * (ε / (|C| + 1)) := by
          refine mul_lt_mul_of_pos_left ?_ (by positivity)
          rw [← dist_eq_norm]; exact hN n hn m hm
      _ = ε := by field_simp
  choose ψt hψt using hpt
  have hcont_n : ∀ n, Continuous (rightConv F (φ n) f) := fun n => (hmc _ (hφmem n)).2
  have hloc : TendstoLocallyUniformly (fun n => rightConv F (φ n) f) ψt Filter.atTop := by
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε g
    obtain ⟨c, u, d₁, d₂, T, hc, hd₁, hWg⟩ := AutomorphicForm.exists_iUnion_centreCutSiegelSet_mem_nhds F g
    obtain ⟨C, hC⟩ := hwin c u d₁ d₂ T hc hd₁
    refine ⟨_, hWg, ?_⟩

    have hev : ∀ᶠ n in Filter.atTop, (|C| + 1) * ‖v - w n‖ < ε := by
      have ht0 : Filter.Tendsto (fun n => v - w n) Filter.atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := v)).sub hw_lim
        rwa [sub_self] at this
      have ht : Filter.Tendsto (fun n => (|C| + 1) * ‖v - w n‖) Filter.atTop (𝓝 ((|C| + 1) * 0)) := by
        have := ht0.norm.const_mul (|C| + 1)
        rwa [norm_zero] at this
      rw [mul_zero] at ht
      exact ht (Iio_mem_nhds hε)
    filter_upwards [hev] with n hn y hy
    have hle : dist (ψt y) (rightConv F (φ n) f y) ≤ (|C| + 1) * ‖v - w n‖ := by
      have hlim := ((hψt y).sub tendsto_const_nhds (b := rightConv F (φ n) f y)).norm
      have hlim2 : Filter.Tendsto (fun m => (|C| + 1) * ‖w m - w n‖) Filter.atTop (𝓝 ((|C| + 1) * ‖v - w n‖)) :=
        ((hw_lim.sub tendsto_const_nhds).norm.const_mul _)
      rw [dist_eq_norm]
      refine le_of_tendsto_of_tendsto' hlim hlim2 fun m => ?_
      calc ‖rightConv F (φ m) f y - rightConv F (φ n) f y‖ ≤ C * ‖w m - w n‖ := hC m n y hy
        _ ≤ (|C| + 1) * ‖w m - w n‖ :=
          mul_le_mul_of_nonneg_right ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one)) (norm_nonneg _)
    exact hle.trans_lt hn
  have hψt_cont : Continuous ψt := hloc.continuous (Filter.Frequently.of_forall hcont_n)

  have hlx_n : ∀ n, IsLsXiFunction (𝓞 F) F ⊤ ξ (rightConv F (φ n) f) := fun n =>
    ((mem_memberSubmodule_iff' F Φ₀ ξ _).mp (hmc _ (hφmem n)).1.1.1).1
  have hψt_lx : IsLsXiFunction (𝓞 F) F ⊤ ξ ψt := by
    refine ⟨fun γ x => ?_, fun z x => ?_⟩
    · exact tendsto_nhds_unique (hψt _) ((hψt x).congr fun n => ((hlx_n n).left_invariant γ x).symm)
    · exact tendsto_nhds_unique (hψt _)
        (((hψt x).const_mul _).congr fun n => ((hlx_n n).central_transform z x).symm)

  have hψt_Kf : IsKfSmooth F ψt := by
    obtain ⟨fa, ff, -, hff, hfac⟩ := hf
    obtain ⟨V, hV1, hV⟩ := IsLocallyConstant.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport hff.1 hff.2
    have h1V : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ∈ V := mem_of_mem_nhds hV1

    have hfinv : ∀ k : ↥(finiteAdelicGL2Subgroup F), glFin (𝓞 F) F ((k : AdelicGL2 (𝓞 F) F)⁻¹) ∈ V →
        ∀ y, f ((k : AdelicGL2 (𝓞 F) F)⁻¹ * y) = f y := by
      intro k hk y
      have harch : glArch (𝓞 F) F ((k : AdelicGL2 (𝓞 F) F)⁻¹) = 1 := by
        rw [map_inv, (mem_finiteAdelicGL2Subgroup_iff F _).mp k.2, inv_one]
      rw [hfac, hfac y, map_mul, harch, one_mul, map_mul]
      have := hV _ hk 1 h1V (glFin (𝓞 F) F y)
      rw [mul_one] at this
      rw [this]

    have hconv_inv : ∀ k : ↥(finiteAdelicGL2Subgroup F), glFin (𝓞 F) F ((k : AdelicGL2 (𝓞 F) F)⁻¹) ∈ V →
        ∀ n x, rightConv F (φ n) f (x * k) = rightConv F (φ n) f x := by
      intro k hk n x
      simp only [rightConv_apply]
      have h1 := integral_mul_left_eq_self (μ := adelicGLHaar (Fin 2) (𝓞 F) F)
        (fun y => φ n (x * (k : AdelicGL2 (𝓞 F) F) * y) * f y) ((k : AdelicGL2 (𝓞 F) F)⁻¹)
      rw [← h1]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      show φ n (x * (k : AdelicGL2 (𝓞 F) F) * ((k : AdelicGL2 (𝓞 F) F)⁻¹ * y)) * f ((k : AdelicGL2 (𝓞 F) F)⁻¹ * y) = φ n (x * y) * f y
      rw [hfinv k hk y, ← mul_assoc, mul_inv_cancel_right]
    have hψt_inv : ∀ k : ↥(finiteAdelicGL2Subgroup F), glFin (𝓞 F) F ((k : AdelicGL2 (𝓞 F) F)⁻¹) ∈ V →
        ∀ x, ψt (x * k) = ψt x := fun k hk x =>
      tendsto_nhds_unique (hψt _) ((hψt x).congr fun n => (hconv_inv k hk n x).symm)

    set Wst : Set ↥(finiteAdelicGL2Subgroup F) := {k | glFin (𝓞 F) F ((k : AdelicGL2 (𝓞 F) F)⁻¹) ∈ V} with hWst
    have hcontk : Continuous fun k : ↥(finiteAdelicGL2Subgroup F) => glFin (𝓞 F) F ((k : AdelicGL2 (𝓞 F) F)⁻¹) :=
      (continuous_glFin (𝓞 F) F).comp (continuous_subtype_val.inv)
    have hWnhds : Wst ∈ 𝓝 (1 : ↥(finiteAdelicGL2Subgroup F)) := by
      refine hcontk.continuousAt.preimage_mem_nhds ?_
      simpa only [OneMemClass.coe_one, inv_one, map_one] using hV1
    refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hWnhds fun k hk => ?_)
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
    rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul, FLT.SmoothVectors.RightTranslationFn.toFun_mk]
    exact hψt_inv k hk x

  have hS8 : ∃ hmem : ψt ∈ memberSubmodule F Φ₀ ξ,
      toCarrier F hΦ₀ σ ξ ⟨ψt, hmem⟩ = ((μ • v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) := by
    have hu : Filter.Tendsto (fun n => ((toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F (φ n) f, hmc _ (hφmem n)⟩ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ))
        Filter.atTop (𝓝 ((μ • v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ)) := (continuous_subtype_val.tendsto _).comp hTlim
    have hsn := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hu
    have hinm := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun n => MeasureTheory.Lp.aestronglyMeasurable _)
      (MeasureTheory.Lp.aestronglyMeasurable _) hsn
    obtain ⟨ns, hns, hae_lim⟩ := hinm.exists_seq_tendsto_ae
    have hrep : ∀ n, ((((toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F (φ n) f, hmc _ (hφmem n)⟩ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) : AdelicGL2 (𝓞 F) F → ℂ))
        =ᵐ[weightedMeasure F Φ₀ σ] rightConv F (φ n) f := fun n => by
      rw [toCuspSubcarrier_apply_coe]
      exact MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem F hΦ₀ σ (hmc _ (hφmem n)).1.1.1)
    have hrep' := ae_all_iff.mpr hrep
    have hLψ : ((((μ • v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) : AdelicGL2 (𝓞 F) F → ℂ)) =ᵐ[weightedMeasure F Φ₀ σ] ψt := by
      filter_upwards [hae_lim, hrep'] with x hx hx'
      have h1 : Filter.Tendsto (fun i => rightConv F (φ (ns i)) f x) Filter.atTop
          (𝓝 ((((μ • v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) : AdelicGL2 (𝓞 F) F → ℂ) x)) := hx.congr fun i => hx' (ns i)
      have h2 : Filter.Tendsto (fun i => rightConv F (φ (ns i)) f x) Filter.atTop (𝓝 (ψt x)) :=
        (hψt x).comp hns.tendsto_atTop
      exact tendsto_nhds_unique h1 h2
    have hmemW : MemLp ψt 2 (weightedMeasure F Φ₀ σ) := (MeasureTheory.Lp.memLp _).ae_eq hLψ
    have hmemΦ : MemLp ψt 2 (μH.restrict Φ₀) :=
      hmemW.of_measure_le_smul (ENNReal.inv_ne_top.mpr hm') hle
    have hmem : ψt ∈ memberSubmodule F Φ₀ ξ := (mem_memberSubmodule_iff' F Φ₀ ξ ψt).mpr ⟨hψt_lx, hmemΦ⟩
    refine ⟨hmem, MeasureTheory.Lp.ext ((MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem F hΦ₀ σ hmem)).trans hLψ.symm)⟩
  obtain ⟨hψt_member, hψt_class⟩ := hS8

  have hψt_cusp : @IsCuspidalFn _ (fdPins F Φ₀).nS _ _ (fdPins F Φ₀).ν unipotentGL2 ψt := by
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
    haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
    haveI hprob : IsProbabilityMeasure ((adelicAddHaar (𝓞 F) F)[|adelicBox F]) := isProbabilityMeasure_cond_adelicBox F
    intro g
    show ∫ q, ψt (unipotentGL2 q * g) ∂((adelicAddHaar (𝓞 F) F)[|adelicBox F]) = 0

    have hn : ∀ n, ∫ q, rightConv F (φ n) f (unipotentGL2 q * g) ∂((adelicAddHaar (𝓞 F) F)[|adelicBox F]) = 0 :=
      fun n => (hmc _ (hφmem n)).1.1.2 g

    obtain ⟨C, hC, hboxC⟩ := exists_isCompact_adelicBox_subset F
    have hu_cont : Continuous fun q : AdeleRing (𝓞 F) F => unipotentGL2 q * g :=
      (continuous_unipotentGL2_adele F).mul continuous_const
    set Kg : Set (AdelicGL2 (𝓞 F) F) := (fun q : AdeleRing (𝓞 F) F => unipotentGL2 q * g) '' C with hKg
    have hKgc : IsCompact Kg := hC.image hu_cont
    have hunif : TendstoUniformlyOn (fun n => rightConv F (φ n) f) ψt Filter.atTop Kg :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hKgc).mp hloc.tendstoLocallyUniformlyOn
    obtain ⟨M, hM⟩ := hKgc.exists_bound_of_continuousOn hψt_cont.continuousOn
    have hev1 := Metric.tendstoUniformlyOn_iff.mp hunif 1 one_pos

    have haeC : ∀ᵐ q ∂((adelicAddHaar (𝓞 F) F)[|adelicBox F]), q ∈ C := by
      rw [ProbabilityTheory.cond]
      exact Measure.ae_smul_measure ((ae_restrict_mem (measurableSet_adelicBox F)).mono fun q hq => hboxC hq) _

    have hlim : Filter.Tendsto (fun n => ∫ q, rightConv F (φ n) f (unipotentGL2 q * g) ∂((adelicAddHaar (𝓞 F) F)[|adelicBox F]))
        Filter.atTop (𝓝 (∫ q, ψt (unipotentGL2 q * g) ∂((adelicAddHaar (𝓞 F) F)[|adelicBox F]))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => M + 1) ?_ ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun n => ((hcont_n n).comp hu_cont).aestronglyMeasurable
      · filter_upwards [hev1] with n hn
        filter_upwards [haeC] with q hq
        have hy : unipotentGL2 q * g ∈ Kg := ⟨q, hq, rfl⟩
        have h1 := hn _ hy
        rw [dist_eq_norm] at h1
        calc ‖rightConv F (φ n) f (unipotentGL2 q * g)‖
            = ‖ψt (unipotentGL2 q * g) - (ψt (unipotentGL2 q * g) - rightConv F (φ n) f (unipotentGL2 q * g))‖ := by
              rw [sub_sub_cancel]
          _ ≤ ‖ψt (unipotentGL2 q * g)‖ + ‖ψt (unipotentGL2 q * g) - rightConv F (φ n) f (unipotentGL2 q * g)‖ := norm_sub_le _ _
          _ ≤ M + 1 := add_le_add (hM _ hy) h1.le
      · exact integrable_const _
      · exact Filter.Eventually.of_forall fun q => hψt _
    have hlim0 : Filter.Tendsto (fun n => ∫ q, rightConv F (φ n) f (unipotentGL2 q * g) ∂((adelicAddHaar (𝓞 F) F)[|adelicBox F]))
        Filter.atTop (𝓝 0) := tendsto_const_nhds.congr fun n => (hn n).symm
    exact tendsto_nhds_unique hlim hlim0

  have hψt_mem : ψt ∈ cuspMemberSubmodule F Φ₀ ξ := ⟨⟨⟨hψt_member, hψt_cusp⟩, hψt_Kf⟩, hψt_cont⟩
  have hψt_cl : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψt, hψt_mem⟩ = μ • v := by
    apply Subtype.ext
    rw [toCuspSubcarrier_apply_coe]
    exact hψt_class
  refine ⟨μ⁻¹ • ψt, Submodule.smul_mem _ _ hψt_mem, ?_, ?_⟩
  · have : (⟨μ⁻¹ • ψt, Submodule.smul_mem _ _ hψt_mem⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = μ⁻¹ • ⟨ψt, hψt_mem⟩ := rfl
    rw [this, map_smul, hψt_cl, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  ·
    have hψm : μ⁻¹ • ψt ∈ cuspMemberSubmodule F Φ₀ ξ := Submodule.smul_mem _ _ hψt_mem
    have hcl : toCuspSubcarrier F hΦ₀ σ ξ ⟨μ⁻¹ • ψt, hψm⟩ = v := by
      have : (⟨μ⁻¹ • ψt, hψm⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = μ⁻¹ • ⟨ψt, hψt_mem⟩ := rfl
      rw [this, map_smul, hψt_cl, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    have hT := hcomm ⟨μ⁻¹ • ψt, hψm⟩ (hmc _ hψm)
    rw [hcl, hv] at hT

    obtain ⟨dψ, hdψ⟩ : ∃ dψ : ↥(cuspMemberSubmodule F Φ₀ ξ), dψ = ⟨_, hmc _ hψm⟩ - μ • ⟨μ⁻¹ • ψt, hψm⟩ := ⟨_, rfl⟩
    have hcl0 : toCuspSubcarrier F hΦ₀ σ ξ dψ = 0 := by
      rw [hdψ, map_sub, map_smul, ← hT, hcl, sub_self]
    have h0 : toCarrier F hΦ₀ σ ξ ⟨(dψ : AdelicGL2 (𝓞 F) F → ℂ), dψ.2.1.1.1⟩ = 0 := by
      have hc := congrArg Subtype.val hcl0
      rw [toCuspSubcarrier_apply_coe, Submodule.coe_zero] at hc
      exact hc
    have hzero := AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ _ ⟨dψ.2.1.1.1, dψ.2.2⟩ h0
    rw [hdψ, Submodule.coe_sub, Submodule.coe_smul, sub_eq_zero] at hzero
    exact hzero

end S_AutomorphicForm_CuspidalSpectrum_exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul (solution)
