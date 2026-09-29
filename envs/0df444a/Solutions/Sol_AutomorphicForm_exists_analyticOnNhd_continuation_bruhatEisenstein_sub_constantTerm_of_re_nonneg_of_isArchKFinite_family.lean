-- Prove2me | solution 1 for AutomorphicForm.exists_analyticOnNhd_continuation_bruhatEisenstein_sub_constantTerm_of_re_nonneg_of_isArchKFinite_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b3a08967-df27-50fb-8067-cdcbcc55eed1

import Theorems.Thm_AutomorphicForm_exists_entire_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
import Theorems.Thm_NumberField_TateGlobal_exists_analyticOnNhd_mul_partialEulerProduct_eq_one_of_isUnitaryChar_of_isIdeleClassChar
import Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient
import Theorems.Thm_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHeight
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_analyticOnNhd_continuation_bruhatEisenstein_sub_constantTerm_of_re_nonneg_of_isArchKFinite_family
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.rightTranslationEmbed_smul_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace R4EContJacquet

open MeasureTheory Set NumberField IsDedekindDomain Filter Metric
open AutomorphicForm NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar NumberField.AdelicHeight
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (F : Type) [Field F] [NumberField F]

abbrev modChar : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

abbrev bigCell (ξ : F) (g : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g

variable {F}

section Helpers

theorem exists_uniformizers :
    ∃ ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ,
      ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
  have h : ∀ v : HeightOneSpectrum (𝓞 F), ∃ π : (v.adicCompletion F)ˣ,
      Valued.v (π : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
    intro v
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have hval : Valued.v ((π : F) : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
      rfl
    have hne : ((π : F) : v.adicCompletion F) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hval
      exact WithZero.zero_ne_coe hval
    exact ⟨Units.mk0 _ hne, hval⟩
  choose ϖ hϖ using h
  exact ⟨ϖ, hϖ⟩

theorem summable_of_summable_subtype_ne_zero {f : F → ℂ}
    (h : Summable (fun ξ : {ξ : F // ξ ≠ 0} => f ξ)) : Summable f := by
  have h' : Summable (f ∘ ((↑) : ↥(({0} : Set F)ᶜ) → F)) := h
  exact ((Set.finite_singleton (0 : F)).summable_compl_iff).mp h'

theorem tsum_eq_zero_add_tsum_subtype {f : F → ℂ} (hf : Summable f) :
    ∑' ξ : F, f ξ = f 0 + ∑' ξ : {ξ : F // ξ ≠ 0}, f ξ := by
  have h := (hf.tsum_subtype_add_tsum_subtype_compl ({0} : Set F))
  rw [tsum_singleton (f := f) 0] at h
  exact h.symm

theorem continuous_of_continuous_val {μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (h : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ)) : Continuous μ := by
  refine Units.continuous_iff.mpr ⟨h, ?_⟩
  have : (fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x)⁻¹ : ℂˣ).val) =
      fun x => (((μ x : ℂˣ) : ℂ))⁻¹ := by
    funext x; simp
  rw [this]
  exact h.inv₀ fun x => Units.ne_zero _

theorem eqOn_half_plane_of_eq_on_one_lt {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {s : ℂ | 1 / 2 < s.re}) (hg : AnalyticOnNhd ℂ g {s : ℂ | 1 / 2 < s.re})
    (h : ∀ s : ℂ, 1 < s.re → f s = g s) : EqOn f g {s : ℂ | 1 / 2 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hpc : IsPreconnected {s : ℂ | 1 / 2 < s.re} := (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have h2' : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
    show (1 / 2 : ℝ) < (2 : ℂ).re
    norm_num
  have hev : f =ᶠ[𝓝 (2 : ℂ)] g :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds h2) fun s hs => h s hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hpc h2' hev

end Helpers

section Godement

theorem norm_etaSnd_apply_of_unitary {ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hν : IsUnitaryChar (𝓞 F) F ν) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ‖((etaSnd ν α hα s x : ℂˣ) : ℂ)‖ = ((α x : ℝˣ) : ℝ) ^ (-(s.re + 1 / 2)) := by
  rw [etaSnd_apply, Units.val_mul, norm_mul, hν x, one_mul, norm_cpowChar_apply]
  congr 1
  rw [Complex.neg_re, re_add_half]

theorem norm_factor {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ)
    (a d : (AdeleRing (𝓞 F) F)ˣ) :
    ‖((etaFst μ α hα s a : ℂˣ) : ℂ) * ((etaSnd ν α hα s d : ℂˣ) : ℂ)‖
      = ((α a : ℝˣ) : ℝ) ^ (s.re + 1 / 2) * ((α d : ℝˣ) : ℝ) ^ (-(s.re + 1 / 2)) := by
  rw [norm_mul, norm_etaFst_apply_of_unitary hμ, norm_etaSnd_apply_of_unitary hν]

theorem norm_height_cpow (σ : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    ‖((adelicHeight F g : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2)‖ = adelicHeight F g ^ (σ + 1 / 2) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos g)]
  congr 1
  simp [Complex.add_re]

theorem uniform_growth (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ (modChar F) hα s) (etaSnd ν (modChar F) hα s) (φ s))
    (hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    {C : Set ℂ} (hC : IsCompact C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ C, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖φ s g‖ ≤ M * adelicHeight F g ^ (s.re + 1 / 2) := by
  set α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ := modChar F with hαdef
  obtain ⟨-, h1u, hsph⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  have hHpow_pos : ∀ (e : ℝ) (g : AdelicGL2 (𝓞 F) F), 0 < adelicHeight F g ^ e := fun e g =>
    Real.rpow_pos_of_pos (adelicHeight_pos g) _

  set q : ℂ × AdelicGL2 (𝓞 F) F → ℝ := fun p => ‖φ p.1 p.2‖ / adelicHeight F p.2 ^ (p.1.re + 1 / 2)
    with hq

  have hq_borel : ∀ (s : ℂ) (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      q (s, b * g) = q (s, g) := by
    intro s b hb g
    set σ : ℝ := s.re with hσ
    have hsphσ := hsph hα (σ : ℂ)
    have h1 : ‖φ s (b * g)‖ = ((α (borelDiagFst ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (σ + 1 / 2)
        * ((α (borelDiagSnd ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (-(σ + 1 / 2)) * ‖φ s g‖ := by
      rw [hφ s b hb g, norm_mul, norm_factor hμ hν α hα s]
    have h2 : adelicHeight F (b * g) ^ (σ + 1 / 2)
        = ((α (borelDiagFst ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (σ + 1 / 2)
          * ((α (borelDiagSnd ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (-(σ + 1 / 2)) * adelicHeight F g ^ (σ + 1 / 2) := by
      have h3 : ((adelicHeight F (b * g) : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) = _ := hsphσ b hb g
      rw [← norm_height_cpow, ← norm_height_cpow, h3, norm_mul, norm_factor h1u h1u α hα (σ : ℂ)]
      simp [Complex.ofReal_re]
    have hpos : 0 < ((α (borelDiagFst ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (σ + 1 / 2)
        * ((α (borelDiagSnd ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (-(σ + 1 / 2)) :=
      mul_pos (Real.rpow_pos_of_pos (hα _) _) (Real.rpow_pos_of_pos (hα _) _)
    simp only [hq]
    rw [h1, h2, mul_div_mul_left _ _ hpos.ne']

  have hq_cont : Continuous q := by
    refine (continuous_norm.comp hφjc).div ?_ fun p => (hHpow_pos _ p.2).ne'
    refine Continuous.rpow ((NumberField.AdelicHeight.continuous_adelicHeight F).comp continuous_snd)
      ((Complex.continuous_re.comp continuous_fst).add continuous_const) fun p => ?_
    exact Or.inl (adelicHeight_pos p.2).ne'

  have hCK : IsCompact (C ×ˢ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F))) :=
    hC.prod (isCompact_adelicMaximalCompact F)
  obtain ⟨M, hM⟩ := hCK.exists_bound_of_continuousOn hq_cont.continuousOn
  have hq_nonneg : ∀ p, 0 ≤ q p := fun p => div_nonneg (norm_nonneg _) (hHpow_pos _ p.2).le
  refine ⟨max M 0, le_max_right _ _, fun s hs g => ?_⟩
  obtain ⟨b, k, hb, hk₁, hk₂, hg⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  have hk : k ∈ adelicMaximalCompact F := ⟨hk₁, hk₂⟩
  have hqsg : q (s, g) ≤ max M 0 := by
    rw [hg, hq_borel s b hb k]
    have := hM (s, k) ⟨hs, hk⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hq_nonneg _)] at this
    exact this.trans (le_max_left _ _)
  have : ‖φ s g‖ = q (s, g) * adelicHeight F g ^ (s.re + 1 / 2) := by
    simp only [hq]; rw [div_mul_cancel₀ _ (hHpow_pos _ g).ne']
  rw [this]
  exact mul_le_mul_of_nonneg_right hqsg (hHpow_pos _ g).le

theorem summable_height_rpow (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    (σ : ℝ) (hσ : 1 / 2 < σ) (g : AdelicGL2 (𝓞 F) F) :
    Summable (fun ξ : F => adelicHeight F (bigCell F ξ g) ^ (σ + 1 / 2)) := by
  obtain ⟨-, h1u, hsph⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  have hsphσ := hsph hα (σ : ℂ)
  have hcont : Continuous (fun g : AdelicGL2 (𝓞 F) F => ((adelicHeight F g : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2)) := by
    refine Continuous.cpow (Complex.continuous_ofReal.comp (NumberField.AdelicHeight.continuous_adelicHeight F))
      continuous_const fun g => Or.inl ?_
    simpa using adelicHeight_pos g
  have hσ' : 1 / 2 < ((σ : ℂ)).re := by simpa using hσ
  have hsum := AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hα 1 1 h1u h1u (σ : ℂ)
    hσ' _ hsphσ hcont g
  refine hsum.congr fun ξ => ?_
  exact norm_height_cpow σ _

theorem rpow_le_rpow_add_rpow {H e elo ehi : ℝ} (hH : 0 < H) (hlo : elo ≤ e) (hhi : e ≤ ehi) :
    H ^ e ≤ H ^ elo + H ^ ehi := by
  rcases le_total H 1 with h1 | h1
  · have := Real.rpow_le_rpow_of_exponent_ge hH h1 hlo
    linarith [Real.rpow_nonneg hH.le ehi]
  · have := Real.rpow_le_rpow_of_exponent_le h1 hhi
    linarith [Real.rpow_nonneg hH.le elo]

theorem majorant (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ (modChar F) hα s) (etaSnd ν (modChar F) hα s) (φ s))
    (hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    {s₀ : ℂ} (hs₀ : 1 / 2 < s₀.re) (g₀ : AdelicGL2 (𝓞 F) F) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K ∈ 𝓝 g₀, ∃ u : F → ℝ, Summable u ∧
      ∀ s ∈ closedBall s₀ ε, ∀ g ∈ K, ∀ ξ : F, ‖φ s (bigCell F ξ g)‖ ≤ u ξ := by
  set ε : ℝ := (s₀.re - 1 / 2) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith

  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds g₀
  have hg₀K : g₀ ∈ K := mem_of_mem_nhds hKn
  set C' : Set (AdelicGL2 (𝓞 F) F) := (fun x => g₀⁻¹ * x) '' K with hC'
  have hC'c : IsCompact C' := hKc.image (continuous_const.mul continuous_id)
  obtain ⟨κ, K', hκ, hbd⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F C' hC'c
  set K'' : ℝ := max K' 1 with hK''
  have hK''1 : 1 ≤ K'' := le_max_right _ _
  have hK''0 : 0 ≤ K'' := zero_le_one.trans hK''1
  have hdist : ∀ g ∈ K, ∀ ξ : F,
      adelicHeight F (bigCell F ξ g) ≤ K'' * adelicHeight F (bigCell F ξ g₀) := by
    intro g hg ξ
    have hx : g₀⁻¹ * g ∈ C' := ⟨g, hg, rfl⟩
    have h1 := (hbd (bigCell F ξ g₀) (g₀⁻¹ * g) hx).2
    have heq : bigCell F ξ g₀ * (g₀⁻¹ * g) = bigCell F ξ g := by
      simp only [bigCell]; group
    rw [heq] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (adelicHeight_pos _).le

  obtain ⟨M, hM0, hM⟩ := uniform_growth hα hμ hν φ hφ hφjc (isCompact_closedBall s₀ ε)

  set elo : ℝ := (s₀.re - ε) + 1 / 2 with helo
  set ehi : ℝ := (s₀.re + ε) + 1 / 2 with hehi
  have hσlo : 1 / 2 < s₀.re - ε := by rw [hε]; linarith
  have hσhi : 1 / 2 < s₀.re + ε := by linarith
  have hexp : ∀ s ∈ closedBall s₀ ε, elo ≤ s.re + 1 / 2 ∧ s.re + 1 / 2 ≤ ehi ∧ 0 ≤ s.re + 1 / 2 := by
    intro s hs
    have h1 : |s.re - s₀.re| ≤ ε := by
      have := Complex.abs_re_le_norm (s - s₀)
      rw [Complex.sub_re] at this
      exact this.trans (mem_closedBall_iff_norm.mp hs)
    rw [abs_le] at h1
    refine ⟨by rw [helo]; linarith, by rw [hehi]; linarith, by linarith⟩

  set H₀ : F → ℝ := fun ξ => adelicHeight F (bigCell F ξ g₀) with hH₀
  refine ⟨ε, hε0, K, hKn, fun ξ => M * K'' ^ ehi * (H₀ ξ ^ elo + H₀ ξ ^ ehi), ?_, ?_⟩
  · exact ((summable_height_rpow hα _ hσlo g₀).add (summable_height_rpow hα _ hσhi g₀)).mul_left _
  · intro s hs g hg ξ
    obtain ⟨hlo, hhi, he0⟩ := hexp s hs
    have hH : 0 < adelicHeight F (bigCell F ξ g) := adelicHeight_pos _
    have hH₀ : 0 < H₀ ξ := adelicHeight_pos _
    calc ‖φ s (bigCell F ξ g)‖
        ≤ M * adelicHeight F (bigCell F ξ g) ^ (s.re + 1 / 2) := hM s hs _
      _ ≤ M * (K'' * H₀ ξ) ^ (s.re + 1 / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hM0
          exact Real.rpow_le_rpow hH.le (hdist g hg ξ) he0
      _ = M * (K'' ^ (s.re + 1 / 2) * H₀ ξ ^ (s.re + 1 / 2)) := by
          rw [Real.mul_rpow hK''0 hH₀.le]
      _ ≤ M * (K'' ^ ehi * (H₀ ξ ^ elo + H₀ ξ ^ ehi)) := by
          refine mul_le_mul_of_nonneg_left ?_ hM0
          refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le hK''1 hhi)
            (rpow_le_rpow_add_rpow hH₀ hlo hhi) (Real.rpow_nonneg hH₀.le _) ?_
          exact Real.rpow_nonneg hK''0 _
      _ = M * K'' ^ ehi * (H₀ ξ ^ elo + H₀ ξ ^ ehi) := by ring

theorem eisenstein_continuousAt (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ (modChar F) hα s) (etaSnd ν (modChar F) hα s) (φ s))
    (hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    (E : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (hE : ∀ s h, E s h = φ s h + ∑' ξ : F, φ s (bigCell F ξ h))
    {s₀ : ℂ} (hs₀ : 1 / 2 < s₀.re) (g₀ : AdelicGL2 (𝓞 F) F) :
    ContinuousAt (fun p : ℂ × AdelicGL2 (𝓞 F) F => E p.1 p.2) (s₀, g₀) := by
  obtain ⟨ε, hε, K, hKn, u, hu, hb⟩ := majorant hα hμ hν φ hφ hφjc hs₀ g₀
  have hS : closedBall s₀ ε ×ˢ K ∈ 𝓝 (s₀, g₀) := prod_mem_nhds (closedBall_mem_nhds _ hε) hKn
  have hT : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => ∑' ξ : F, φ p.1 (bigCell F ξ p.2))
      (closedBall s₀ ε ×ˢ K) := by
    refine continuousOn_tsum (fun ξ => ?_) hu fun ξ p hp => hb p.1 hp.1 p.2 hp.2 ξ
    exact (hφjc.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd))).continuousOn
  have hT' : ContinuousAt (fun p : ℂ × AdelicGL2 (𝓞 F) F => ∑' ξ : F, φ p.1 (bigCell F ξ p.2)) (s₀, g₀) :=
    hT.continuousAt hS
  have hfun : (fun p : ℂ × AdelicGL2 (𝓞 F) F => E p.1 p.2)
      = fun p => φ p.1 p.2 + ∑' ξ : F, φ p.1 (bigCell F ξ p.2) := funext fun p => hE _ _
  rw [hfun]
  exact hφjc.continuousAt.add hT'

theorem eisenstein_differentiableAt (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ (modChar F) hα s) (etaSnd ν (modChar F) hα s) (φ s))
    (hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    (hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
    (E : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (hE : ∀ s h, E s h = φ s h + ∑' ξ : F, φ s (bigCell F ξ h))
    {s₀ : ℂ} (hs₀ : 1 / 2 < s₀.re) (g : AdelicGL2 (𝓞 F) F) :
    DifferentiableAt ℂ (fun s => E s g) s₀ := by
  obtain ⟨ε, hε, K, hKn, u, hu, hb⟩ := majorant hα hμ hν φ hφ hφjc hs₀ g
  have hgK : g ∈ K := mem_of_mem_nhds hKn
  have hball : DifferentiableOn ℂ (fun s => ∑' ξ : F, φ s (bigCell F ξ g)) (ball s₀ ε) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hu (fun ξ => (hφhol _).differentiableOn)
      isOpen_ball ?_
    intro ξ s hs
    exact hb s (ball_subset_closedBall hs) g hgK ξ
  have hT : DifferentiableAt ℂ (fun s => ∑' ξ : F, φ s (bigCell F ξ g)) s₀ :=
    hball.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hε))
  have hfun : (fun s => E s g) = fun s => φ s g + ∑' ξ : F, φ s (bigCell F ξ g) := funext fun s => hE _ _
  rw [hfun]
  exact (hφhol g s₀).add hT

end Godement

section ConstantTerm

variable (F)

scoped instance isProbabilityMeasure_cond_adelicBox' :
    IsProbabilityMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) :=
  isProbabilityMeasure_cond_adelicBox F

variable {F}

theorem analyticOnNhd_constantTerm {O : Set ℂ} (hO : IsOpen O) {Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hEa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Ec s g) O)
    (hEjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ec p.1 p.2) (O ×ˢ Set.univ))
    (h : AdelicGL2 (𝓞 F) F) :
    AnalyticOnNhd ℂ (fun s => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => unipotentGL2 t) (Ec s) h) O := by

  obtain ⟨Cb, hCb, hboxCb⟩ := exists_isCompact_adelicBox_subset F
  obtain ⟨χ, hχ1, -, hχc, hχ01⟩ :=
    exists_continuous_one_zero_of_isCompact hCb isClosed_empty (Set.disjoint_empty _)
  set ν₀ : Measure (AdeleRing (𝓞 F) F) := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F) with hν₀
  set G : ℂ → AdeleRing (𝓞 F) F → ℂ := fun z t => ((χ t : ℝ) : ℂ) * Ec z (unipotentGL2 t * h) with hG

  have hmap : ContinuousOn (fun p : ℂ × AdeleRing (𝓞 F) F => ((p.1, unipotentGL2 p.2 * h) : ℂ × AdelicGL2 (𝓞 F) F))
      (O ×ˢ Set.univ) :=
    (continuous_fst.prodMk ((AutomorphicForm.continuous_unipotentGL2.comp continuous_snd).mul
      continuous_const)).continuousOn
  have hmaps : Set.MapsTo (fun p : ℂ × AdeleRing (𝓞 F) F => ((p.1, unipotentGL2 p.2 * h) : ℂ × AdelicGL2 (𝓞 F) F))
      (O ×ˢ Set.univ) (O ×ˢ Set.univ) := fun p hp => ⟨hp.1, Set.mem_univ _⟩
  have hEc2 : ContinuousOn (fun p : ℂ × AdeleRing (𝓞 F) F => Ec p.1 (unipotentGL2 p.2 * h)) (O ×ˢ Set.univ) :=
    hEjc.comp hmap hmaps
  have hGc : ContinuousOn (Function.uncurry G) (O ×ˢ Set.univ) := by
    have hχc' : Continuous fun p : ℂ × AdeleRing (𝓞 F) F => ((χ p.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (χ.continuous.comp continuous_snd)
    exact hχc'.continuousOn.mul hEc2
  have hGS : ∀ z ∈ O, ∀ a ∉ tsupport χ, G z a = 0 := by
    intro z hz a ha
    simp only [hG, image_eq_zero_of_notMem_tsupport ha, Complex.ofReal_zero, zero_mul]
  have hGhol : ∀ a : AdeleRing (𝓞 F) F, DifferentiableOn ℂ (fun z => G z a) O := fun a =>
    (differentiableOn_const _).mul (hEa _).differentiableOn
  have hd : DifferentiableOn ℂ (fun z => ∫ a, G z a ∂ν₀) O :=
    Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn ν₀ hO hχc.isCompact G hGc hGS hGhol

  have heq : ∀ z ∈ O, ∫ a, G z a ∂ν₀
      = constantTerm ν₀ (fun t => unipotentGL2 t) (Ec z) h := by
    intro z hz
    unfold constantTerm constantTermIntegrand
    refine integral_congr_ae ?_
    have hae : ∀ᵐ t ∂ν₀, t ∈ adelicBox F := ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox F)
    filter_upwards [hae] with t ht
    have h1 : χ t = 1 := hχ1 (hboxCb ht)
    simp only [hG, h1, Complex.ofReal_one, one_mul]
  have hd' : DifferentiableOn ℂ (fun z => constantTerm ν₀ (fun t => unipotentGL2 t) (Ec z) h) O :=
    hd.congr fun z hz => (heq z hz).symm
  exact hd'.analyticOnNhd hO

end ConstantTerm

section Main

variable (F)

theorem main
    (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμic : IsIdeleClassChar (𝓞 F) F μ) (hνic : IsIdeleClassChar (𝓞 F) F ν)
    (hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ (modChar F) hα s) (etaSnd ν (modChar F) hα s) (φ s))
    (hφK : ∀ s, IsArchKFinite F (φ s))
    (hφf : ∀ s, IsKfSmooth F (φ s))
    (hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    (hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
    (E : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (hE : ∀ s h, E s h = φ s h + ∑' ξ : F, φ s (bigCell F ξ h)) :
    ∃ (U : Set ℂ) (V : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      IsOpen U ∧ {s : ℂ | 0 ≤ s.re} ⊆ U ∧
      (∀ h : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => V s h) U) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => V p.1 p.2) (U ×ˢ Set.univ) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        V s h = E s h -
          constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => unipotentGL2 t) (E s) h) := by
  classical

  set ψ : AddChar (AdeleRing (𝓞 F) F) ℂ := NumberField.StandardAddChar.stdAddChar F with hψdef
  have hψ : IsGlobalAddChar F ψ := (NumberField.StandardAddChar.adelicTraceData F).isGlobalAddChar_psiK
  have hEfun : E = fun s h => φ s h + ∑' ξ : F, φ s (bigCell F ξ h) := funext fun s => funext fun h => hE s h
  obtain ⟨S₀, hS₀⟩ :=
    AutomorphicForm.exists_entire_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
      F hα μ ν hμ hν hμic hνic ψ hψ φ hφ hφK hφf hφjc hφhol
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizers (F := F)
  obtain ⟨𝒲, h1, h2, h3, h4, -⟩ := hS₀ S₀ (Finset.Subset.refl _) ϖ hϖ

  let Vn : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h => ∑' ξ : {ξ : F // ξ ≠ 0}, 𝒲 ξ s h
  have hVn_diff : ∀ h, Differentiable ℂ (fun s => Vn s h) := by
    intro h s₀
    obtain ⟨u, hu, hub⟩ := h4 (closedBall s₀ 1) {h} (isCompact_closedBall _ _) isCompact_singleton
    have hball : DifferentiableOn ℂ (fun s => Vn s h) (ball s₀ 1) := by
      refine Complex.differentiableOn_tsum_of_summable_norm hu (fun ξ => (h1 ξ h).differentiableOn)
        isOpen_ball ?_
      intro ξ w hw
      exact hub ξ w (ball_subset_closedBall hw) h (Set.mem_singleton _)
    exact hball.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))

  have hVn_cont : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => Vn p.1 p.2) := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    obtain ⟨s₀, h₀⟩ := p
    obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds h₀
    obtain ⟨u, hu, hub⟩ := h4 (closedBall s₀ 1) K (isCompact_closedBall _ _) hKc
    have hon : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Vn p.1 p.2) (closedBall s₀ 1 ×ˢ K) := by
      refine continuousOn_tsum (fun ξ => (h3 ξ).continuousOn) hu fun ξ p hp => ?_
      exact hub ξ p.1 hp.1 p.2 hp.2
    exact hon.continuousAt (prod_mem_nhds (closedBall_mem_nhds _ one_pos) hKn)

  set χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := μ * ν⁻¹ with hχdef
  have hμc : Continuous μ := continuous_of_continuous_val hμk
  have hνc : Continuous ν := continuous_of_continuous_val hνk
  have hχc : Continuous χ := by
    have : (χ : (AdeleRing (𝓞 F) F)ˣ → ℂˣ) = fun x => μ x * (ν x)⁻¹ := by
      funext x; simp [hχdef]
    rw [this]
    exact hμc.mul hνc.inv
  have hχu : IsUnitaryChar (𝓞 F) F χ := by
    intro x
    simp only [hχdef, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      norm_mul, norm_inv, hμ x, hν x]
    norm_num
  have hχF : IsIdeleClassChar (𝓞 F) F χ := by
    intro u
    simp only [hχdef, MonoidHom.mul_apply, MonoidHom.inv_apply, hμic u, hνic u, inv_one, mul_one]
  obtain ⟨UL, P, hULo, hULsub, hPan, hPL⟩ :=
    NumberField.TateGlobal.exists_analyticOnNhd_mul_partialEulerProduct_eq_one_of_isUnitaryChar_of_isIdeleClassChar
      F S₀ ϖ hϖ χ hχc hχu hχF

  let Z : ℂ → ℂ := fun s => ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₀},
    (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
      * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹
  have hZP : ∀ s : ℂ, Z s = ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₀},
      (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
        * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹ := fun s => rfl
  have hre : ∀ s : ℂ, 1 < s.re → 1 < (2 * s + 1).re := by
    intro s hs
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re]
    linarith
  have hPZ : ∀ s : ℂ, 1 < s.re → P (2 * s + 1) * Z s = 1 := fun s hs => hPL (2 * s + 1) (hre s hs)
  have hZne : ∀ s : ℂ, 1 < s.re → Z s ≠ 0 := fun s hs => right_ne_zero_of_mul_eq_one (hPZ s hs)

  let aff : ℂ → ℂ := fun s => 2 * s + 1
  have haff_cont : Continuous aff := (continuous_const.mul continuous_id).add continuous_const
  have haff_an : AnalyticOnNhd ℂ aff Set.univ :=
    (((differentiable_id.const_mul (2 : ℂ)).add_const 1).differentiableOn.analyticOnNhd isOpen_univ)
  let U : Set ℂ := aff ⁻¹' UL
  have hUo : IsOpen U := hULo.preimage haff_cont
  have hUsub : {s : ℂ | 0 ≤ s.re} ⊆ U := by
    intro s hs
    refine hULsub ?_
    show (1 : ℝ) ≤ (2 * s + 1).re
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re]
    have : (0 : ℝ) ≤ s.re := hs
    linarith
  let V : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h => P (aff s) * Vn s h
  have hPaff : AnalyticOnNhd ℂ (fun s => P (aff s)) U :=
    hPan.comp (haff_an.mono (Set.subset_univ _)) fun s hs => hs
  have hVan : ∀ h, AnalyticOnNhd ℂ (fun s => V s h) U := fun h =>
    hPaff.mul (((hVn_diff h).differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _))
  have hVjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => V p.1 p.2) (U ×ˢ Set.univ) := by
    have h1 : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => P (aff p.1)) (U ×ˢ Set.univ) := by
      refine hPan.continuousOn.comp (haff_cont.comp continuous_fst).continuousOn ?_
      intro p hp
      exact hp.1
    exact h1.mul hVn_cont.continuousOn

  have hident : ∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 < s.re →
      Vn s h = Z s * (E s h -
        constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) (E s) h) := by
    intro s h hs
    have hs' : 1 / 2 < s.re := by linarith

    have hφc : Continuous (φ s) := hφjc.comp (Continuous.prodMk_right s)
    have hEc : Continuous (E s) := by
      rw [hEfun]
      exact hφc.add (AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half F hα μ ν hμ hν s hs' (φ s)
        (hφ s) hφc)
    have hslice : Continuous (fun x : AdeleRing (𝓞 F) F => E s (unipotentGL2 x * h)) :=
      hEc.comp ((AutomorphicForm.continuous_unipotentGL2).mul continuous_const)

    let f : F → ℂ := fun ξ => whittakerCoefficient F (productionPins F) ψ (E s) ξ h
    obtain ⟨u, hu, hub⟩ := h4 {s} {h} isCompact_singleton isCompact_singleton
    have hZs : Z s ≠ 0 := hZne s hs
    have hfW : ∀ ξ : {ξ : F // ξ ≠ 0}, f ξ = (Z s)⁻¹ * 𝒲 ξ s h := by
      intro ξ
      show whittakerCoefficient F (productionPins F) ψ (E s) ξ h = _
      rw [hEfun, h2 ξ s h hs, ← hZP s, ← mul_assoc, inv_mul_cancel₀ hZs, one_mul]
    have hsub : Summable (fun ξ : {ξ : F // ξ ≠ 0} => f ξ) := by
      have hb : ∀ ξ : {ξ : F // ξ ≠ 0}, ‖f ξ‖ ≤ ‖(Z s)⁻¹‖ * u ξ := by
        intro ξ
        rw [hfW ξ, norm_mul]
        exact mul_le_mul_of_nonneg_left (hub ξ s (Set.mem_singleton _) h (Set.mem_singleton _)) (norm_nonneg _)
      exact Summable.of_norm_bounded (hu.mul_left _) hb
    have hsumF : Summable f := summable_of_summable_subtype_ne_zero hsub

    have hHas : HasSum f (E s h) :=
      AutomorphicForm.hasSum_whittakerCoefficient F
        (AutomorphicForm.WindowedSiegel.centreCutSiegelSet F (1/2 : ℝ) 1 (1/2) 2)
        (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) ψ hψ (E s) h hslice hsumF
    have hsplit : E s h = f 0 + ∑' ξ : {ξ : F // ξ ≠ 0}, f ξ := by
      rw [← hHas.tsum_eq]
      exact tsum_eq_zero_add_tsum_subtype hsumF

    have hf0 : f 0 = constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        (fun t => unipotentGL2 t) (E s) h := by
      show whittakerCoefficient F (productionPins F) ψ (E s) 0 h = _
      rw [whittakerCoefficient_zero_eq_constantTerm]
      rfl

    have hV : Vn s h = ∑' ξ : {ξ : F // ξ ≠ 0}, Z s * f ξ := by
      show (∑' ξ : {ξ : F // ξ ≠ 0}, 𝒲 ξ s h) = _
      refine tsum_congr (fun ξ => ?_)
      rw [hfW ξ, ← mul_assoc, mul_inv_cancel₀ hZs, one_mul]
    rw [hV, tsum_mul_left, ← hf0]
    congr 1
    rw [hsplit]
    ring

  set Hh : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hHh
  have hHo : IsOpen Hh := isOpen_lt continuous_const Complex.continuous_re
  have hEan : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => E s g) Hh := by
    intro g
    have hd : DifferentiableOn ℂ (fun s => E s g) Hh := fun s hs =>
      (eisenstein_differentiableAt hα hμ hν φ hφ hφjc hφhol E hE hs g).differentiableWithinAt
    exact hd.analyticOnNhd hHo
  have hEjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => E p.1 p.2) (Hh ×ˢ Set.univ) := by
    rintro ⟨s, g⟩ hp
    exact (eisenstein_continuousAt hα hμ hν φ hφ hφjc E hE hp.1 g).continuousWithinAt
  have hCTan : ∀ h : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ
      (fun s => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        (fun t => unipotentGL2 t) (E s) h) Hh := fun h =>
    analyticOnNhd_constantTerm hHo hEan hEjc h

  refine ⟨U, V, hUo, hUsub, hVan, hVjc, ?_⟩
  intro s h hs
  have hHU : Hh ⊆ U := by
    intro z hz
    refine hUsub ?_
    have hz' : (1 / 2 : ℝ) < z.re := hz
    show (0 : ℝ) ≤ z.re
    linarith
  have hVh : AnalyticOnNhd ℂ (fun z => V z h) Hh := (hVan h).mono hHU
  have hDh : AnalyticOnNhd ℂ (fun z => E z h -
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        (fun t => unipotentGL2 t) (E z) h) Hh := (hEan h).sub (hCTan h)
  refine eqOn_half_plane_of_eq_on_one_lt hVh hDh (fun z hz => ?_) hs
  show P (aff z) * Vn z h = _
  rw [hident z h hz, ← mul_assoc, hPZ z hz, one_mul]

end Main

end R4EContJacquet
p2m_reactivate "P2MW.S_AutomorphicForm_exists_analyticOnNhd_continuation_bruhatEisenstein_sub_constantTerm_of_re_nonneg_of_isArchKFinite_family.R4EContJacquet"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_analyticOnNhd_continuation_bruhatEisenstein_sub_constantTerm_of_re_nonneg_of_isArchKFinite_family.R4EContJacquet"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open scoped NNReal

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W),
    letI := adeleBorel (𝓞 F) F
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    ∃ (U : Set ℂ) (V : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      IsOpen U ∧ {s : ℂ | 0 ≤ s.re} ⊆ U ∧
      (∀ h : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => V s h) U) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => V p.1 p.2) (U ×ˢ Set.univ) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        V s h = E s h -
          constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => unipotentGL2 t) (E s) h) := by
  intro α hα μ ν hμ hν hμic hνic hμk hνk φ hφ hφK hφf hφjc hφhol _hφKu E
  exact R4EContJacquet.main F hα μ ν hμ hν hμic hνic hμk hνk φ hφ hφK hφf hφjc hφhol E (fun s h => rfl)

end S_AutomorphicForm_exists_analyticOnNhd_continuation_bruhatEisenstein_sub_constantTerm_of_re_nonneg_of_isArchKFinite_family
end P2MW
export P2MW.S_AutomorphicForm_exists_analyticOnNhd_continuation_bruhatEisenstein_sub_constantTerm_of_re_nonneg_of_isArchKFinite_family (solution)
