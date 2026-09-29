-- Prove2me | solution 1 for AutomorphicForm.exists_forall_integrable_prod_sum_rightConv_mul_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_symm_of_subset_iUnion_image_centreCutSiegelSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/cf091bc6-d723-5816-8efd-0e4ad3dcb1e0

import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2
import Theorems.Thm_AutomorphicForm_exists_forall_norm_constantTerm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_half_of_flat
import Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_AutomorphicForm_adelicHeight_sigmaAdelicAct
import Theorems.Thm_AutomorphicForm_constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Order.Compact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_integrable_prod_sum_rightConv_mul_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_symm_of_subset_iUnion_image_centreCutSiegelSet
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"
p2m_attr_erase "simp" "EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace R4DomSigma

open MeasureTheory Set NumberField IsDedekindDomain Filter
open AutomorphicForm NumberField.AdelicHaar NumberField.AdelicHeight NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel
open scoped ComplexConjugate NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section RealAnalysis

theorem norm_sum_sum_mul_le {n : ℕ} (a : Fin n → Fin n → ℂ) (u v : Fin n → ℂ) {P : ℝ}
    (hP : ∀ i j, ‖u i‖ * ‖v j‖ ≤ P) :
    ‖∑ i, ∑ j, a i j * (u i * conj (v j))‖ ≤ (∑ i, ∑ j, ‖a i j‖) * P := by
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (hP i j) (norm_nonneg _)

theorem one_le_gauge {ι : Type*} [Fintype ι] (v : ι → ℂ) : (1 : ℝ) ≤ 1 + ∑ w, ‖v w‖ :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem rpow_neg_add_mul_pow {x : ℝ} (hx : 1 ≤ x) (M k : ℕ) :
    x ^ (-((M + k : ℕ) : ℝ)) * x ^ k = x ^ (-(M : ℝ)) := by
  have hx0 : 0 < x := one_pos.trans_le hx
  rw [← Real.rpow_natCast x k, ← Real.rpow_add hx0]
  congr 1
  push_cast
  ring

theorem rpow_neg_natCast_nonneg {x : ℝ} (hx : 1 ≤ x) (M : ℕ) : 0 ≤ x ^ (-(M : ℝ)) :=
  Real.rpow_nonneg (zero_le_one.trans hx) _

end RealAnalysis

section Profile

variable {ι' : Type*} [Fintype ι'] (a b : ι' → ℝ)

theorem one_le_profile (t : ℝ) : 1 ≤ 1 + ∑ v, (|t + a v| + |t - b v|) :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem weighted_profile_le (mμ mν : ι' → ℤ) (M₀ : ℕ)
    (hm : ∀ v, |mμ v| ≤ (M₀ : ℤ) ∧ |mν v| ≤ (M₀ : ℤ)) (t : ℝ) :
    (1 + ∑ v, (|t + a v| + |t - b v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ≤
      (1 + 2 * Fintype.card ι' * M₀) * (1 + ∑ v, (|t + a v| + |t - b v|)) := by
  have h1 : ∀ v, (|t + a v| + |t - b v| + (|mμ v| : ℝ) + (|mν v| : ℝ)) ≤
      (|t + a v| + |t - b v|) + 2 * M₀ := by
    intro v
    have hμ : (|mμ v| : ℝ) ≤ M₀ := by exact_mod_cast (hm v).1
    have hν : (|mν v| : ℝ) ≤ M₀ := by exact_mod_cast (hm v).2
    linarith
  have h2 : (∑ v, (|t + a v| + |t - b v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ≤
      (∑ v, (|t + a v| + |t - b v|)) + 2 * Fintype.card ι' * M₀ := by
    calc (∑ v, (|t + a v| + |t - b v| + (|mμ v| : ℝ) + (|mν v| : ℝ)))
        ≤ ∑ v, ((|t + a v| + |t - b v|) + 2 * M₀) := Finset.sum_le_sum fun v _ => h1 v
      _ = (∑ v, (|t + a v| + |t - b v|)) + 2 * Fintype.card ι' * M₀ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have h3 : (0 : ℝ) ≤ 2 * Fintype.card ι' * M₀ := by positivity
  have h4 := one_le_profile a b t
  nlinarith

end Profile

section OnK

theorem integral_mul_conj_self (L : Type) [Field L] [NumberField L] (x : adelicMaximalCompact L → ℂ) :
    (∫ k, x k * conj (x k) ∂(maximalCompactHaar L)) =
      ((∫ k, ‖x k‖ ^ 2 ∂(maximalCompactHaar L) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [Complex.mul_conj', Complex.ofReal_pow]

end OnK

section Iwasawa

theorem modulus_ratio_eq (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
      ((α (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) /
          ((α (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) =
        adelicHeight F b / adelicHeight F 1 := by
  intro α hα b hb
  have h := (AutomorphicForm.isInducedSection_adelicHeight_cpow F).2.2 hα ((1 : ℂ) / 2) b hb 1
  have h12 : (1 : ℂ) / 2 + 1 / 2 = 1 := by norm_num
  simp only [mul_one, h12, Complex.cpow_one, etaFst_apply, etaSnd_apply,
    MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val, Complex.cpow_neg_one] at h
  have hpos1 : 0 < adelicHeight F 1 := adelicHeight_pos 1
  have h' : adelicHeight F b =
      ((α (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) *
        (((α (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ))⁻¹ * adelicHeight F 1 := by
    exact_mod_cast h
  rw [eq_div_iff hpos1.ne', h', div_eq_mul_inv]

theorem exists_borel_mul_maximalCompact (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    ∃ b k : AdelicGL2 (𝓞 F) F, b ∈ adelicBorel (𝓞 F) F ∧ k ∈ adelicMaximalCompact F ∧ g = b * k ∧
      adelicHeight F b = adelicHeight F g := by
  obtain ⟨b, k, hb, hkf, hka, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  have hk : k ∈ adelicMaximalCompact F := ⟨hkf, hka⟩
  exact ⟨b, k, hb, hk, rfl, (adelicHeight_mul_of_mem_adelicMaximalCompact F b k hk).symm⟩

theorem sqrt_le_div_sqrt {h₀ H : ℝ} (hh₀ : 0 < h₀) (hle : h₀ ≤ H) : Real.sqrt H ≤ H / Real.sqrt h₀ := by
  have hH : 0 ≤ H := hh₀.le.trans hle
  rw [le_div_iff₀ (Real.sqrt_pos.2 hh₀), ← Real.sqrt_mul hH]
  calc Real.sqrt (H * h₀) ≤ Real.sqrt (H * H) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle hH)
    _ = H := Real.sqrt_mul_self hH

end Iwasawa

section Measurability

variable (K : Type) [Field K] [NumberField K]

theorem measurable_lambdaT_family
    (Φ : ℝ → AdelicGL2 (𝓞 K) K → ℂ) (hΦ : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => Φ p.1 p.2)
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (T : ℝ) :
    Measurable fun p : ℝ × AdelicGL2 (𝓞 K) K =>
      @AutomorphicForm.lambdaT _ (productionPinsOf K D U gen (adelicBox K)).nS _ _
        (productionPinsOf K D U gen (adelicBox K)).ν (fun t => AutomorphicForm.unipotentGL2 t)
        (NumberField.AdelicHeight.adelicHeight K) T (Φ p.1) p.2 := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  show Measurable fun p : ℝ × AdelicGL2 (𝓞 K) K =>
    lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun t => unipotentGL2 t)
      (adelicHeight K) T (Φ p.1) p.2
  have hCT : StronglyMeasurable fun p : ℝ × AdelicGL2 (𝓞 K) K =>
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
        (fun t => unipotentGL2 t) (Φ p.1) p.2 := by
    have h1 : Continuous fun q : (ℝ × AdelicGL2 (𝓞 K) K) × AdeleRing (𝓞 K) K =>
        (q.1.1, unipotentGL2 q.2 * q.1.2) :=
      (continuous_fst.comp continuous_fst).prodMk
        ((AutomorphicForm.continuous_unipotentGL2.comp continuous_snd).mul
          (continuous_snd.comp continuous_fst))
    have hc : Continuous fun q : (ℝ × AdelicGL2 (𝓞 K) K) × AdeleRing (𝓞 K) K =>
        Φ q.1.1 (unipotentGL2 q.2 * q.1.2) := hΦ.comp h1
    haveI : IsFiniteMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) := by
      haveI := isProbabilityMeasure_cond_adelicBox K
      infer_instance
    have h := hc.stronglyMeasurable
    unfold constantTerm constantTermIntegrand
    exact h.integral_prod_right'
  have hH : MeasurableSet {p : ℝ × AdelicGL2 (𝓞 K) K | T < adelicHeight K p.2} :=
    measurableSet_lt measurable_const
      ((NumberField.AdelicHeight.continuous_adelicHeight K).measurable.comp measurable_snd)
  have hE : Measurable fun p : ℝ × AdelicGL2 (𝓞 K) K => Φ p.1 p.2 := hΦ.measurable
  have heq : (fun p : ℝ × AdelicGL2 (𝓞 K) K =>
      lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun t => unipotentGL2 t)
        (adelicHeight K) T (Φ p.1) p.2) =
      fun p => Φ p.1 p.2 -
        {p : ℝ × AdelicGL2 (𝓞 K) K | T < adelicHeight K p.2}.indicator
          (fun p => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
            (fun t => unipotentGL2 t) (Φ p.1) p.2) p := by
    funext p
    rw [lambdaT_apply]
    by_cases h : T < adelicHeight K p.2
    · rw [Set.indicator_of_mem (mem_highSet_iff.2 h),
        Set.indicator_of_mem (show p ∈ {p : ℝ × AdelicGL2 (𝓞 K) K | T < adelicHeight K p.2} from h)]
    · rw [Set.indicator_of_notMem (fun h' => h (mem_highSet_iff.1 h')),
        Set.indicator_of_notMem (show p ∉ {p : ℝ × AdelicGL2 (𝓞 K) K | T < adelicHeight K p.2} from h)]
  rw [heq]
  exact hE.sub ((hCT.measurable).indicator hH)

end Measurability

section Floor

variable (F : Type) [Field F] [NumberField F]

theorem pow_le_adelicHeight_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hc : 0 ≤ c)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u d₁ d₂) :
    c ^ (∑ w : InfinitePlace F, w.mult) ≤ adelicHeight F g := by
  have h := centreCutSiegelSet_subset_integralWindowedSiegelSet (F := F) (u := u) (d₁ := d₁)
    (d₂ := d₂) hc hg
  obtain ⟨hK, hfloor, -⟩ := h
  rw [adelicHeight_eq_archHeight_of_mem hK]
  exact hfloor

theorem exists_floor (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 F) F)) (hTc : IsCompact Tc)
    (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' centreCutSiegelSet F c u d₁ d₂) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ g ∈ Φ₀, h₀ ≤ adelicHeight F g := by
  obtain ⟨κ, K, hκ, hκK⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F Tc hTc
  set h₀ : ℝ := κ * c ^ (∑ w : InfinitePlace F, w.mult) with hh₀
  have hcpow : 0 < c ^ (∑ w : InfinitePlace F, w.mult) := pow_pos hc _
  have hh₀pos : 0 < h₀ := mul_pos hκ hcpow
  refine ⟨h₀, hh₀pos, fun g hg => ?_⟩
  have hg' := hΦ₀S hg
  simp only [Set.mem_iUnion, Set.mem_image] at hg'
  obtain ⟨y, hy, x, hx, rfl⟩ := hg'
  have h1 : c ^ (∑ w : InfinitePlace F, w.mult) ≤ adelicHeight F x :=
    pow_le_adelicHeight_of_mem_centreCutSiegelSet F hc.le hx
  have h2 : κ * adelicHeight F x ≤ adelicHeight F (x * y) := (hκK x y hy).1
  calc h₀ = κ * c ^ (∑ w : InfinitePlace F, w.mult) := rfl
    _ ≤ κ * adelicHeight F x := mul_le_mul_of_nonneg_left h1 hκ.le
    _ ≤ adelicHeight F (x * y) := h2

end Floor

section Domain

variable (K : Type) [Field K] [NumberField K]

theorem measure_lt_top_of_isFundamentalDomain_slab {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    adelicGLHaar (Fin 2) (𝓞 K) K Φ₀ < ⊤ := by
  have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
    K α β hα hαβ _ hΦ₀
  rwa [Set.inter_eq_self_of_subset_left hΦ₀s] at h

theorem ae_mem_of_isFundamentalDomain_slab {α β : ℝ}
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∀ᵐ x ∂(adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀, x ∈ Φ₀ := by
  set H := adelicGLHaar (Fin 2) (𝓞 K) K
  have hnm : NullMeasurableSet Φ₀ (H.restrict Φ₀) := by
    have h1 : NullMeasurableSet Φ₀ (H.restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) :=
      hΦ₀.nullMeasurableSet
    refine h1.mono_ac (Measure.absolutelyContinuous_of_le ?_)
    exact Measure.restrict_mono hΦ₀s le_rfl
  rw [ae_iff]
  have h2 : (H.restrict Φ₀) Φ₀ᶜ = H (Φ₀ᶜ ∩ Φ₀) := Measure.restrict_apply₀ hnm.compl
  have h3 : Φ₀ᶜ ∩ Φ₀ = ∅ := Set.compl_inter_self Φ₀
  rw [h3, measure_empty] at h2
  exact h2

end Domain

section Unipotent

variable (L : Type) [Field L] [NumberField L]

theorem unipotentGL2_algebraMap (k : L) :
    unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) k) = globalPoints (𝓞 L) L (unipotentGL2 k) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (!![(1 : AdeleRing (𝓞 L) L), algebraMap L (AdeleRing (𝓞 L) L) k; 0, 1]) i j =
    algebraMap L (AdeleRing (𝓞 L) L) ((!![(1 : L), k; 0, 1]) i j)
  fin_cases i <;> fin_cases j <;> simp

theorem axis_continuation_unipotent_mul
    (φ : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
    (hφN : ∀ (s : ℂ) (x : AdeleRing (𝓞 L) L) (g : AdelicGL2 (𝓞 L) L), φ s (unipotentGL2 x * g) = φ s g)
    (O : Set ℂ) (E : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
    (hOc : IsPreconnected O) (hhalf : {s : ℂ | 1 / 2 < s.re} ⊆ O)
    (hEan : ∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => E s g) O)
    (hEeq : ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        E s g = φ s g + ∑' ξ : L, φ s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g))
    (k : L) {s : ℂ} (hs : s ∈ O) (g : AdelicGL2 (𝓞 L) L) :
    E s (unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) k) * g) = E s g := by
  set nk := unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) k) with hnk
  set Fd : ℂ → ℂ := fun z => E z (nk * g) - E z g with hFd
  have hFan : AnalyticOnNhd ℂ Fd O := (hEan (nk * g)).sub (hEan g)

  have hzero : ∀ z : ℂ, 1 / 2 < z.re → Fd z = 0 := by
    intro z hz
    simp only [hFd]
    rw [hEeq z hz (nk * g), hEeq z hz g, hφN, sub_eq_zero]
    congr 1
    have hterm : ∀ ξ : L, φ z (adelicWeyl (𝓞 L) L * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * (nk * g)) =
        φ z (adelicWeyl (𝓞 L) L * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) (ξ + k)) * g) := by
      intro ξ
      rw [map_add, unipotentGL2_add, hnk]
      congr 1
      simp only [mul_assoc]
    simp_rw [hterm]
    exact (Equiv.addRight k).tsum_eq
      (fun ξ' : L => φ z (adelicWeyl (𝓞 L) L * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ') * g))

  have h1mem : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
    show (1 / 2 : ℝ) < (1 : ℂ).re
    norm_num
  have hev : Fd =ᶠ[𝓝 (1 : ℂ)] 0 := by
    have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds h1mem] with z hz
    exact hzero z hz
  have hEq := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hOc (hhalf h1mem) hev
  have h0 : Fd s = 0 := hEq hs
  simpa only [hFd, sub_eq_zero] using h0

end Unipotent

end R4DomSigma

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option maxHeartbeats 16000000 in
open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξu : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξu ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξu ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hξu : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ‖((ξu ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 L) L (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 L) L (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 L) L (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 L) L (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 L) L)ˣ), μ e z * ν e z = ξu ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles L,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 L) L (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite L (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth L (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 L) L), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace L), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => φE e j s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact L),
        φE e j s (k : AdelicGL2 (𝓞 L) L) = φE e j 0 (k : AdelicGL2 (𝓞 L) L))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule L tysL)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 L) L) * conj (φE e j 0 (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 L) L μ' → IsUnitaryChar (𝓞 L) L ν' →
        IsIdeleClassChar (𝓞 L) L μ' → IsIdeleClassChar (𝓞 L) L ν' →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ' z * ν' z = ξu ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        EE e j s g = φE e j s g + ∑' ξ : L, φE e j s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        NE e j s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (φE e j s) g))
      (f : AdelicGL2 (𝓞 L) L → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn L f →
      IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) f →
      IsArchBiFinite L tysL f →
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ e : ιE, Integrable (fun p : ℝ × AdelicGL2 (𝓞 L) L => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv L (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) * conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L))
              ∂(maximalCompactHaar L)) *
            (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
              conj ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((p.1 : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                p.2))))
          ((volume : Measure ℝ).prod ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀))) ∧
      (Summable fun e : ιE => ∫ p : ℝ × AdelicGL2 (𝓞 L) L, ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv L (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) * conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L))
              ∂(maximalCompactHaar L)) *
            (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
              conj ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((p.1 : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                p.2)))‖
          ∂((volume : Measure ℝ).prod ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀))) ∧
      (∀ (e : ιE) (i j : Fin (nE e)) (t : ℝ),
        IntegrableOn (fun x : AdelicGL2 (𝓞 L) L =>
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                x) *
              conj (EE e i ((t : ℂ) * Complex.I) x))
          Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
        IntegrableOn (fun x : AdelicGL2 (𝓞 L) L =>
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                x) *
              conj ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (EE e i ((t : ℂ) * Complex.I))
                x)))
          Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L)) := by
  intro αm hαm ιE _cnt μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat
    hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE f hf hfc hfact hbi harch
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := NumberField.AdelicHaar.adeleBorel (𝓞 L) L
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 L) L
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  have hHc : Continuous (NumberField.AdelicHeight.adelicHeight L) :=
    NumberField.AdelicHeight.continuous_adelicHeight L
  have hHpos : ∀ g, 0 < NumberField.AdelicHeight.adelicHeight L g :=
    fun g => NumberField.AdelicHeight.adelicHeight_pos g
  have hH1 : 0 < NumberField.AdelicHeight.adelicHeight L 1 := hHpos 1

  have hξw : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ‖((ξu ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm L z) ^ ((0 : ℝ)) : ℝ) := by
    intro z
    rw [hξu z, Real.rpow_zero]
  have hμν0 : ∀ (e : ιE) (z : (AdeleRing (𝓞 L) L)ˣ),
      ((μ e z : ℂˣ) : ℂ) * ((ν e z : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm L z) ^ ((0 : ℝ)) : ℝ) : ℂ) =
        ((ξu ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
    intro e z
    rw [Real.rpow_zero, Complex.ofReal_one, mul_one, ← Units.val_mul, hμν e z]
  have hpairs0 : ∀ (μ' ν' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
      IsUnitaryChar (𝓞 L) L μ' → IsUnitaryChar (𝓞 L) L ν' →
      IsIdeleClassChar (𝓞 L) L μ' → IsIdeleClassChar (𝓞 L) L ν' →
      (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μ' z : ℂˣ) : ℂ)) →
      (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ν' z : ℂˣ) : ℂ)) →
      (∀ z : (AdeleRing (𝓞 L) L)ˣ,
        ((μ' z : ℂˣ) : ℂ) * ((ν' z : ℂˣ) : ℂ) *
            (((NumberField.TateGlobal.ideleNorm L z) ^ ((0 : ℝ)) : ℝ) : ℂ) =
          ((ξu ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
      ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
      IsInducedSection (𝓞 L) L (etaFst μ' αm hαm ((t : ℂ) * Complex.I))
        (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
      Continuous φ₀ → IsArchKFinite L φ₀ →
      (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
        φ₀ (g * u) = φ₀ g) →
      φ₀ ∈ archCutSubmodule L tysL → φ₀ ≠ 0 →
      ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, μ e z = μ' z ∧ ν e z = ν' z := by
    intro μ' ν' h1 h2 h3 h4 h5 h6 h7
    refine hpairs μ' ν' h1 h2 h3 h4 h5 h6 (fun z => ?_)
    have h := h7 z
    rw [Real.rpow_zero, Complex.ofReal_one, mul_one, ← Units.val_mul] at h
    exact Units.val_injective h

  obtain ⟨TK, cK, hcK, uK, hcov⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet L
  have hcovK := hcov 1 2 two_pos one_le_two

  obtain ⟨D₀, τμ, τν, mμ, mν, Mw, nρ, ρs, M₀, hcard, hτ, hm, hMw, -, hB⟩ :=
    AutomorphicForm.exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2
      L α β hα hαβ ΦL cK uK 1 2 TK hcK one_pos one_lt_two hcovK νZL ΩL hΩL SL ξu hξc hξt N hN tysL
      (fun _ => 0) (fun _ _ => 0) 0 hξw hαm ιE μ ν hμ hν hμic hνic hμc hνc hμν0 hdist nE φE hφE hφEK hφEf
      hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs0 OE EE NE hEE
  have hτμ : ∀ (e : ιE) (v : InfinitePlace L) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
        (((NumberField.TateGlobal.ideleNorm L (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
          (((τμ e v : ℝ) : ℂ) * Complex.I) := fun e v x h1 h2 => (hτ e v x h1 h2).1
  have hτν : ∀ (e : ιE) (v : InfinitePlace L) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((NumberField.TateGlobal.archLocalChar (ν e) v x : ℂˣ) : ℂ) =
        (((NumberField.TateGlobal.ideleNorm L (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
          (((τν e v : ℝ) : ℂ) * Complex.I) := fun e v x h1 h2 => (hτ e v x h1 h2).2
  have hmμ : ∀ (e : ιE) (v : InfinitePlace L) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ e v) :=
    fun e v x h1 => (hm e v x h1).1
  have hmν : ∀ (e : ιE) (v : InfinitePlace L) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((NumberField.TateGlobal.archLocalChar (ν e) v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν e v) :=
    fun e v x h1 => (hm e v x h1).2

  set Λ : ιE → ℝ → ℝ := fun e t =>
    1 + ∑ v : InfinitePlace L, (|t + τμ e v| + |t - τν e v|) with hΛdef
  have hΛ1 : ∀ e t, 1 ≤ Λ e t := fun e t => R4DomSigma.one_le_profile (τμ e) (τν e) t
  have hΛ0 : ∀ e t, 0 ≤ Λ e t := fun e t => zero_le_one.trans (hΛ1 e t)
  have hΛpos : ∀ e t, 0 < Λ e t := fun e t => one_pos.trans_le (hΛ1 e t)
  have hΛpow0 : ∀ e t (A : ℕ), 0 ≤ Λ e t ^ A := fun e t A => pow_nonneg (hΛ0 e t) A

  set Pl : ℝ := (Fintype.card (InfinitePlace L) : ℝ) with hPl
  set Rm : ℝ := 1 + 2 * Pl * Mw with hRmdef
  have hRm1 : 1 ≤ Rm := by
    have h0 : (0 : ℝ) ≤ 2 * Pl * (Mw : ℝ) := by positivity
    rw [hRmdef]; linarith
  have hRm0 : 0 ≤ Rm := zero_le_one.trans hRm1
  have hGw : ∀ (e : ιE), 0 < nE e → ∀ (t : ℝ) (A : ℕ),
      (1 + ∑ v : InfinitePlace L, (|t + τμ e v| + |t - τν e v| + (|mμ e v| : ℝ) + (|mν e v| : ℝ))) ^ A ≤
        Rm ^ A * Λ e t ^ A := by
    intro e he t A
    have h := R4DomSigma.weighted_profile_le (τμ e) (τν e) (mμ e) (mν e) Mw (hMw e he) t
    have h0 : (0 : ℝ) ≤ 1 + ∑ v : InfinitePlace L, (|t + τμ e v| + |t - τν e v| + (|mμ e v| : ℝ) + (|mν e v| : ℝ)) :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun v _ => by positivity)
    calc (1 + ∑ v : InfinitePlace L, (|t + τμ e v| + |t - τν e v| + (|mμ e v| : ℝ) + (|mν e v| : ℝ))) ^ A
        ≤ (Rm * Λ e t) ^ A := pow_le_pow_left₀ h0 h A
      _ = Rm ^ A * Λ e t ^ A := mul_pow _ _ _

  have hΛint' : ∀ e, Integrable (fun t : ℝ => Λ e t ^ (-(M₀ : ℝ))) := fun e => (hB M₀ le_rfl).1 e
  have hΛsum0 : Summable fun e : ιE => if 0 < nE e then ∫ t : ℝ, Λ e t ^ (-(M₀ : ℝ)) else (0 : ℝ) :=
    (hB M₀ le_rfl).2.1
  have hΛsum' : Summable fun e : ιE => if nE e = 0 then (0 : ℝ) else ∫ t : ℝ, Λ e t ^ (-(M₀ : ℝ)) := by
    refine hΛsum0.congr fun e => ?_
    by_cases he : nE e = 0
    · simp [he]
    · simp [he, Nat.pos_of_ne_zero he]

  obtain ⟨CT0, AT, hCT0, hCTG⟩ :=
    AutomorphicForm.exists_forall_norm_constantTerm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_half_of_flat
      L SL ξu hξc hξt N hN tysL 0 hξw

  obtain ⟨h₀, hh₀, hfloor⟩ := R4DomSigma.exists_floor L c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S
  obtain ⟨c', hc'def⟩ : ∃ c' : ℝ, c' = h₀ / NumberField.AdelicHeight.adelicHeight L 1 := ⟨_, rfl⟩
  have hc' : 0 < c' := by rw [hc'def]; exact div_pos hh₀ hH1
  obtain ⟨CU0, AU, hCU0, hUDEC⟩ :=
    AutomorphicForm.exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
      L SL ξu hξc hξt N hN tysL 0 hξw (adelicMaximalCompact L : Set (AdelicGL2 (𝓞 L) L))
      (isCompact_adelicMaximalCompact L) c' hc' 1

  have hφn : ∀ e j, (∫ k, ‖φE e j 0 (k : AdelicGL2 (𝓞 L) L)‖ ^ 2 ∂(maximalCompactHaar L)) ≤ 1 := by
    intro e j
    have h1 := hφEon e j j
    rw [if_pos rfl, R4DomSigma.integral_mul_conj_self] at h1
    have h2 : (∫ k, ‖φE e j 0 (k : AdelicGL2 (𝓞 L) L)‖ ^ 2 ∂(maximalCompactHaar L)) = 1 := by exact_mod_cast h1
    exact h2.le

  obtain ⟨A₂, hA₂def⟩ : ∃ A : ℕ, A = AT + AU := ⟨_, rfl⟩
  obtain ⟨A₃, hA₃def⟩ : ∃ A : ℕ, A = AU := ⟨_, rfl⟩
  obtain ⟨B₂, hB₂def⟩ : ∃ B : ℕ, B = 1 := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂def⟩ : ∃ C : ℝ, C = CT0 * Rm ^ AT / Real.sqrt h₀ +
    CU0 * Rm ^ AU * NumberField.AdelicHeight.adelicHeight L 1 / h₀ ^ 2 := ⟨_, rfl⟩
  obtain ⟨c₃, hc₃def⟩ : ∃ C : ℝ, C = CU0 * Rm ^ AU * NumberField.AdelicHeight.adelicHeight L 1 := ⟨_, rfl⟩

  have h3 : ∀ (e : ιE) (i : Fin (nE e)) (t : ℝ) (z : AdelicGL2 (𝓞 L) L),
      h₀ ≤ NumberField.AdelicHeight.adelicHeight L z →
        ‖EE e i ((t : ℂ) * Complex.I) z -
            AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun q => AutomorphicForm.unipotentGL2 q) (EE e i ((t : ℂ) * Complex.I)) z‖ ≤
          c₃ * Λ e t ^ A₃ * (NumberField.AdelicHeight.adelicHeight L z)⁻¹ ^ B₂ := by
    intro e i t z hz
    have he : 0 < nE e := Fin.pos i
    have hHz := hHpos z
    obtain ⟨b, k, hb, hk, hzbk, hHb⟩ := R4DomSigma.exists_borel_mul_maximalCompact L z
    have hratio := R4DomSigma.modulus_ratio_eq L hαm b hb
    rw [hHb] at hratio

    have hcr : c' ≤ ((αm (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))) : ℝˣ) : ℝ) /
        ((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))) : ℝˣ) : ℝ) := by
      rw [hratio, hc'def]
      exact div_le_div_of_nonneg_right hz hH1.le
    have hU := hUDEC hαm (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (hμν0 e)
      (τμ e) (τν e) (hτμ e) (hτν e) (mμ e) (mν e) (hmμ e) (hmν e) (φE e i) (hφE e i) (hφEK e i)
      (hφEf e i) (hφEjc e i) (hφEhol e i) (hφEKu e i) (hφEflat e i) (hφElev e i) (hφEty e i) (hφn e i)
      (OE e i) (EE e i) (NE e i) (hEE e i) t ⟨b, hb⟩ k hk hcr
    have hbk : ((⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L)) : AdelicGL2 (𝓞 L) L) * k = z := hzbk.symm
    simp only [hratio, hbk] at hU
    refine hU.trans ?_

    have hpow : (NumberField.AdelicHeight.adelicHeight L z / NumberField.AdelicHeight.adelicHeight L 1) ^
        (-((1 : ℕ) : ℝ)) = NumberField.AdelicHeight.adelicHeight L 1 * (NumberField.AdelicHeight.adelicHeight L z)⁻¹ := by
      rw [Nat.cast_one, Real.rpow_neg_one, inv_div, div_eq_mul_inv]
    rw [hpow, hB₂def, pow_one]
    have hG := hGw e he t AU
    have hx0 : 0 ≤ NumberField.AdelicHeight.adelicHeight L 1 * (NumberField.AdelicHeight.adelicHeight L z)⁻¹ :=
      mul_nonneg hH1.le (inv_nonneg.2 hHz.le)
    calc CU0 * (1 + ∑ v : InfinitePlace L, (|t + τμ e v| + |t - τν e v| + (|mμ e v| : ℝ) + (|mν e v| : ℝ))) ^ AU *
          (NumberField.AdelicHeight.adelicHeight L 1 * (NumberField.AdelicHeight.adelicHeight L z)⁻¹)
        ≤ CU0 * (Rm ^ AU * Λ e t ^ AU) *
          (NumberField.AdelicHeight.adelicHeight L 1 * (NumberField.AdelicHeight.adelicHeight L z)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hCU0.le) hx0
      _ = c₃ * Λ e t ^ A₃ * (NumberField.AdelicHeight.adelicHeight L z)⁻¹ := by
          rw [hc₃def, hA₃def]; ring

  have h2 : ∀ (e : ιE) (i : Fin (nE e)) (t : ℝ) (z : AdelicGL2 (𝓞 L) L),
      h₀ ≤ NumberField.AdelicHeight.adelicHeight L z →
        ‖EE e i ((t : ℂ) * Complex.I) z‖ ≤
          c₂ * Λ e t ^ A₂ * NumberField.AdelicHeight.adelicHeight L z ^ B₂ := by
    intro e i t z hz
    have he : 0 < nE e := Fin.pos i
    have hHz := hHpos z

    have hT := hCTG hαm (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (hμν0 e)
      (τμ e) (τν e) (hτμ e) (hτν e) (mμ e) (mν e) (hmμ e) (hmν e) (φE e i) (hφE e i) (hφEK e i)
      (hφEf e i) (hφEjc e i) (hφEhol e i) (hφEKu e i) (hφEflat e i) (hφElev e i) (hφEty e i) (hφn e i)
      (OE e i) (EE e i) (NE e i) (hEE e i) t z
    rw [← Real.sqrt_eq_rpow] at hT

    have hDz := h3 e i t z hz
    rw [hB₂def, pow_one] at hDz
    have hGT := hGw e he t AT
    have hGU := hGw e he t AU
    have hsq : Real.sqrt (NumberField.AdelicHeight.adelicHeight L z) ≤ (NumberField.AdelicHeight.adelicHeight L z) / Real.sqrt h₀ := R4DomSigma.sqrt_le_div_sqrt hh₀ hz
    have hsqrt0 : 0 < Real.sqrt h₀ := Real.sqrt_pos.2 hh₀
    have hΛA : Λ e t ^ AT ≤ Λ e t ^ A₂ := pow_le_pow_right₀ (hΛ1 e t) (hA₂def ▸ Nat.le_add_right AT AU)
    have hΛU : Λ e t ^ AU ≤ Λ e t ^ A₂ := pow_le_pow_right₀ (hΛ1 e t) (hA₂def ▸ Nat.le_add_left AU AT)
    have hΛ3 : Λ e t ^ A₃ ≤ Λ e t ^ A₂ := by rw [hA₃def]; exact hΛU

    have hT1 : ‖AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))
        (fun q => AutomorphicForm.unipotentGL2 q) (EE e i ((t : ℂ) * Complex.I)) z‖ ≤
        (CT0 * Rm ^ AT / Real.sqrt h₀) * Λ e t ^ A₂ * (NumberField.AdelicHeight.adelicHeight L z) := by
      refine hT.trans ?_
      calc CT0 * (1 + ∑ v : InfinitePlace L, (|t + τμ e v| + |t - τν e v| + (|mμ e v| : ℝ) + (|mν e v| : ℝ))) ^ AT *
            Real.sqrt (NumberField.AdelicHeight.adelicHeight L z)
          ≤ CT0 * (Rm ^ AT * Λ e t ^ A₂) * ((NumberField.AdelicHeight.adelicHeight L z) / Real.sqrt h₀) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (hGT.trans ?_) hCT0.le) hsq (Real.sqrt_nonneg _)
              (mul_nonneg hCT0.le (mul_nonneg (pow_nonneg hRm0 _) (hΛpow0 e t _)))
            exact mul_le_mul_of_nonneg_left hΛA (pow_nonneg hRm0 _)
        _ = (CT0 * Rm ^ AT / Real.sqrt h₀) * Λ e t ^ A₂ * (NumberField.AdelicHeight.adelicHeight L z) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]; ring

    have hz1 : 1 ≤ (NumberField.AdelicHeight.adelicHeight L z) / h₀ := by rwa [le_div_iff₀ hh₀, one_mul]
    have hT2 : ‖EE e i ((t : ℂ) * Complex.I) z -
        AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun q => AutomorphicForm.unipotentGL2 q) (EE e i ((t : ℂ) * Complex.I)) z‖ ≤
        (CU0 * Rm ^ AU * (NumberField.AdelicHeight.adelicHeight L 1) / h₀ ^ 2) * Λ e t ^ A₂ * (NumberField.AdelicHeight.adelicHeight L z) := by
      refine hDz.trans ?_
      have hinv : (NumberField.AdelicHeight.adelicHeight L z)⁻¹ ≤ h₀⁻¹ := inv_anti₀ hh₀ hz
      have hc30 : 0 ≤ c₃ := by rw [hc₃def]; exact mul_nonneg (mul_nonneg hCU0.le (pow_nonneg hRm0 _)) hH1.le
      calc c₃ * Λ e t ^ A₃ * (NumberField.AdelicHeight.adelicHeight L z)⁻¹
          ≤ c₃ * Λ e t ^ A₂ * h₀⁻¹ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hΛ3 hc30) hinv (inv_nonneg.2 hHz.le)
              (mul_nonneg hc30 (hΛpow0 e t _))
        _ ≤ c₃ * Λ e t ^ A₂ * h₀⁻¹ * ((NumberField.AdelicHeight.adelicHeight L z) / h₀) :=
            le_mul_of_one_le_right (mul_nonneg (mul_nonneg hc30 (hΛpow0 e t _)) (inv_nonneg.2 hh₀.le)) hz1
        _ = (CU0 * Rm ^ AU * (NumberField.AdelicHeight.adelicHeight L 1) / h₀ ^ 2) * Λ e t ^ A₂ * (NumberField.AdelicHeight.adelicHeight L z) := by
            rw [hc₃def, div_eq_mul_inv, div_eq_mul_inv]; ring

    have hsplit : ‖EE e i ((t : ℂ) * Complex.I) z‖ ≤
        ‖AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))
            (fun q => AutomorphicForm.unipotentGL2 q) (EE e i ((t : ℂ) * Complex.I)) z‖ +
          ‖EE e i ((t : ℂ) * Complex.I) z -
            AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun q => AutomorphicForm.unipotentGL2 q) (EE e i ((t : ℂ) * Complex.I)) z‖ := by
      have := norm_add_le
        (AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun q => AutomorphicForm.unipotentGL2 q) (EE e i ((t : ℂ) * Complex.I)) z)
        (EE e i ((t : ℂ) * Complex.I) z -
          AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))
            (fun q => AutomorphicForm.unipotentGL2 q) (EE e i ((t : ℂ) * Complex.I)) z)
      rwa [add_sub_cancel] at this
    calc ‖EE e i ((t : ℂ) * Complex.I) z‖
        ≤ (CT0 * Rm ^ AT / Real.sqrt h₀) * Λ e t ^ A₂ * (NumberField.AdelicHeight.adelicHeight L z) + (CU0 * Rm ^ AU * (NumberField.AdelicHeight.adelicHeight L 1) / h₀ ^ 2) * Λ e t ^ A₂ * (NumberField.AdelicHeight.adelicHeight L z) :=
          hsplit.trans (add_le_add hT1 hT2)
      _ = c₂ * Λ e t ^ A₂ * (NumberField.AdelicHeight.adelicHeight L z) ^ B₂ := by rw [hc₂def, hB₂def, pow_one]; ring

  obtain ⟨Cc, hCc0, hcoef⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn
      L SL ξu hξc hξt N hN tysL 0 hξw f hf hfc hfact (M₀ + (A₂ + A₂ + A₃))
  have hw : ∀ (e : ιE) (j : Fin (nE e)) (s : ℂ), (fun g : AdelicGL2 (𝓞 L) L => φE e j s g *
      (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ ((0 : ℝ) / 2) : ℝ) : ℂ)) =
      φE e j s := by
    intro e j s
    funext g
    rw [zero_div, Real.rpow_zero, Complex.ofReal_one, mul_one]
  have hcoef' : ∀ (e : ιE) (i j : Fin (nE e)), ∃ a' : ℝ → ℂ,
      (∀ t : ℝ, HasDerivAt (fun t : ℝ =>
        ∫ k, rightConv L (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
          conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) (a' t) t) ∧
      Continuous a' ∧
      ∀ t : ℝ, ‖∫ k, rightConv L (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
          conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)‖ + ‖a' t‖ ≤
        Cc * (1 + ∑ v : InfinitePlace L, (|t + τμ e v| + |t - τν e v|)) ^ (-((M₀ + (A₂ + A₂ + A₃) : ℕ) : ℝ)) := by
    intro e i j
    have h := hcoef hαm (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (hμν0 e)
      (τμ e) (τν e) (hτμ e) (hτν e) (φE e i) (φE e j) (hφE e i) (hφE e j) (hφEK e i) (hφEK e j)
      (hφEf e i) (hφEf e j) (hφEjc e i) (hφEjc e j) (hφEhol e i) (hφEhol e j) (hφEKu e i) (hφEKu e j)
      (hφEflat e i) (hφEflat e j) (hφElev e i) (hφElev e j) (hφEty e i) (hφEty e j) (hφn e i) (hφn e j)
    simp only [hw] at h
    exact h
  choose aD haD haDc hbd using hcoef'

  have hacont : ∀ (e : ιE) (i j : Fin (nE e)), Continuous fun t : ℝ =>
      ∫ k, rightConv L (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
        conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L) := by
    intro e i j
    have hd : Differentiable ℝ (fun t : ℝ =>
        ∫ k, rightConv L (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
          conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) :=
      fun t => (haD e i j t).differentiableAt
    exact hd.continuous

  obtain ⟨c₁, hc₁def⟩ : ∃ C : ℝ, C = (D₀ : ℝ) * D₀ * Cc := ⟨_, rfl⟩
  have h1 : ∀ (e : ιE) (t : ℝ),
      (∑ i : Fin (nE e), ∑ j : Fin (nE e),
        ‖∫ k, rightConv L (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
            conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)‖) ≤
        c₁ * Λ e t ^ (-((M₀ + (A₂ + A₂ + A₃) : ℕ) : ℝ)) := by
    intro e t
    have hx0 : 0 ≤ Cc * Λ e t ^ (-((M₀ + (A₂ + A₂ + A₃) : ℕ) : ℝ)) :=
      mul_nonneg hCc0.le (Real.rpow_nonneg (hΛ0 e t) _)
    have hone : ∀ i j : Fin (nE e),
        ‖∫ k, rightConv L (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
            conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)‖ ≤
          Cc * Λ e t ^ (-((M₀ + (A₂ + A₂ + A₃) : ℕ) : ℝ)) := by
      intro i j
      have h := hbd e i j t
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans h
    have hcardR : (nE e : ℝ) ≤ D₀ := Nat.cast_le.mpr (hcard e)
    calc (∑ i : Fin (nE e), ∑ j : Fin (nE e),
          ‖∫ k, rightConv L (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
              conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)‖)
        ≤ ∑ _i : Fin (nE e), ∑ _j : Fin (nE e), Cc * Λ e t ^ (-((M₀ + (A₂ + A₂ + A₃) : ℕ) : ℝ)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hone i j
      _ = (nE e : ℝ) * ((nE e : ℝ) * (Cc * Λ e t ^ (-((M₀ + (A₂ + A₂ + A₃) : ℕ) : ℝ)))) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (D₀ : ℝ) * ((D₀ : ℝ) * (Cc * Λ e t ^ (-((M₀ + (A₂ + A₂ + A₃) : ℕ) : ℝ)))) := by
          have hx1 : 0 ≤ (nE e : ℝ) * (Cc * Λ e t ^ (-((M₀ + (A₂ + A₂ + A₃) : ℕ) : ℝ))) := mul_nonneg (Nat.cast_nonneg _) hx0
          exact mul_le_mul hcardR (mul_le_mul_of_nonneg_right hcardR hx0) hx1 (Nat.cast_nonneg _)
      _ = c₁ * Λ e t ^ (-((M₀ + (A₂ + A₂ + A₃) : ℕ) : ℝ)) := by rw [hc₁def]; ring

  have hempty : ∀ e, nE e = 0 → ∀ (F : Fin (nE e) → Fin (nE e) → ℂ),
      (∑ i : Fin (nE e), ∑ j : Fin (nE e), F i j) = 0 := by
    intro e he F
    have : IsEmpty (Fin (nE e)) := by rw [he]; infer_instance
    simp [Finset.univ_eq_empty]

  have hHσ : ∀ x : AdelicGL2 (𝓞 L) L,
      NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.sigmaAdelicAct K L D σ.symm x) =
        NumberField.AdelicHeight.adelicHeight L x :=
    fun x => AutomorphicForm.adelicHeight_sigmaAdelicAct K L D σ.symm x
  have hu : ∀ (e : ιE) (j : Fin (nE e)) (t : ℝ) (k : L) (x : AdelicGL2 (𝓞 L) L),
      EE e j ((t : ℂ) * Complex.I) (globalPoints (𝓞 L) L (AutomorphicForm.unipotentGL2 k) * x) =
        EE e j ((t : ℂ) * Complex.I) x := by
    intro e j t k x
    obtain ⟨-, hOc, hax, hhalf, hEan, -, -, -, hEeq, -⟩ := hEE e j
    rw [← R4DomSigma.unipotentGL2_algebraMap]
    exact R4DomSigma.axis_continuation_unipotent_mul L (φE e j)
      (fun s y g => AutomorphicForm.isInducedSection_unipotent_mul (hφE e j s) y g) (OE e j) (EE e j)
      hOc hhalf hEan hEeq k (hax (by simp)) x

  set pins := productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
    (fun w => heckeGen (𝓞 L) L w) (adelicBox L) with hpinsdef
  have hCTeq : ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L),
      @AutomorphicForm.constantTerm _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t) φ g =
        AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun q => AutomorphicForm.unipotentGL2 q) φ g := fun _ _ => rfl
  have hΛσ : ∀ (e : ιE) (j : Fin (nE e)) (t : ℝ) (T : ℝ) (x : AdelicGL2 (𝓞 L) L),
      (@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) T
          (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y)) x) =
        @AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) T
          (EE e j ((t : ℂ) * Complex.I)) (AutomorphicForm.sigmaAdelicAct K L D σ.symm x) := by
    intro e j t T x
    exact (AutomorphicForm.constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn K L D σ.symm ΦL
      (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w)
      (EE e j ((t : ℂ) * Complex.I)) (hu e j t)).2 T x

  refine ⟨0, fun R _ => ?_⟩
  set c₁' := max c₁ 0 with hc₁'def
  set c₂' := max c₂ 0 with hc₂'def
  set c₃' := max c₃ 0 with hc₃'def
  have hc₁'0 : 0 ≤ c₁' := le_max_right _ _
  have hc₂'0 : 0 ≤ c₂' := le_max_right _ _
  have hc₃'0 : 0 ≤ c₃' := le_max_right _ _
  set CR : ℝ := c₂' ^ 2 * Real.exp R ^ (B₂ + B₂) + c₂' * c₃' with hCRdef
  have hCR0 : 0 ≤ CR :=
    add_nonneg (mul_nonneg (pow_nonneg hc₂'0 2) (pow_nonneg (Real.exp_pos R).le _)) (mul_nonneg hc₂'0 hc₃'0)
  set CR2 : ℝ := c₂' ^ 2 * Real.exp R ^ (B₂ + B₂) + c₃' ^ 2 * h₀⁻¹ ^ (B₂ + B₂) with hCR2def
  have hCR20 : 0 ≤ CR2 :=
    add_nonneg (mul_nonneg (pow_nonneg hc₂'0 2) (pow_nonneg (Real.exp_pos R).le _))
      (mul_nonneg (pow_nonneg hc₃'0 2) (pow_nonneg (inv_nonneg.2 hh₀.le) _))

  have hE : ∀ (e : ιE) (i : Fin (nE e)) (t : ℝ) (z : AdelicGL2 (𝓞 L) L),
      h₀ ≤ NumberField.AdelicHeight.adelicHeight L z →
        ‖EE e i ((t : ℂ) * Complex.I) z‖ ≤
          c₂' * Λ e t ^ A₂ * NumberField.AdelicHeight.adelicHeight L z ^ B₂ := by
    intro e i t z hz
    refine (h2 e i t z hz).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (hΛpow0 e t A₂))
      (pow_nonneg (hHpos _).le _)

  have hD : ∀ (e : ιE) (i : Fin (nE e)) (t : ℝ) (z : AdelicGL2 (𝓞 L) L),
      h₀ ≤ NumberField.AdelicHeight.adelicHeight L z →
        ‖EE e i ((t : ℂ) * Complex.I) z -
            AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun q => AutomorphicForm.unipotentGL2 q) (EE e i ((t : ℂ) * Complex.I)) z‖ ≤
          c₃' * Λ e t ^ A₃ * (NumberField.AdelicHeight.adelicHeight L z)⁻¹ ^ B₂ := by
    intro e i t z hz
    refine (h3 e i t z hz).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (hΛpow0 e t A₃))
      (pow_nonneg (inv_nonneg.2 (hHpos _).le) _)

  have hΛE : ∀ (e : ιE) (j : Fin (nE e)) (t : ℝ) (z : AdelicGL2 (𝓞 L) L),
      h₀ ≤ NumberField.AdelicHeight.adelicHeight L z →
      NumberField.AdelicHeight.adelicHeight L z ≤ Real.exp R →
        ‖(@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (EE e j ((t : ℂ) * Complex.I))) z‖ ≤ c₂' * Λ e t ^ A₂ * Real.exp R ^ B₂ := by
    intro e j t z hz hle
    rw [AutomorphicForm.lambdaT_apply_of_le _ _ hle]
    refine (hE e j t z hz).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hHpos z).le hle _) (mul_nonneg hc₂'0 (hΛpow0 e t A₂))
  have hΛD : ∀ (e : ιE) (j : Fin (nE e)) (t : ℝ) (z : AdelicGL2 (𝓞 L) L),
      h₀ ≤ NumberField.AdelicHeight.adelicHeight L z →
      Real.exp R < NumberField.AdelicHeight.adelicHeight L z →
        ‖(@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (EE e j ((t : ℂ) * Complex.I))) z‖ ≤
          c₃' * Λ e t ^ A₃ * (NumberField.AdelicHeight.adelicHeight L z)⁻¹ ^ B₂ := by
    intro e j t z hz hcut
    rw [AutomorphicForm.lambdaT_apply_of_lt _ _ hcut, hCTeq]
    exact hD e j t z hz

  have hprod : ∀ (e : ιE) (i j : Fin (nE e)) (t : ℝ) (z z' : AdelicGL2 (𝓞 L) L),
      NumberField.AdelicHeight.adelicHeight L z' = NumberField.AdelicHeight.adelicHeight L z →
      h₀ ≤ NumberField.AdelicHeight.adelicHeight L z →
        ‖EE e i ((t : ℂ) * Complex.I) z‖ *
          ‖(@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (EE e j ((t : ℂ) * Complex.I))) z'‖ ≤ CR * Λ e t ^ (A₂ + A₂ + A₃) := by
    intro e i j t z z' hzz hz
    have hHz := hHpos z
    have hz' : h₀ ≤ NumberField.AdelicHeight.adelicHeight L z' := by rw [hzz]; exact hz
    have hEi := hE e i t z hz
    by_cases hcut : Real.exp R < NumberField.AdelicHeight.adelicHeight L z
    ·
      have hcut' : Real.exp R < NumberField.AdelicHeight.adelicHeight L z' := by rw [hzz]; exact hcut
      have hEj := hΛD e j t z' hz' hcut'
      rw [hzz] at hEj
      calc ‖EE e i ((t : ℂ) * Complex.I) z‖ * _
          ≤ (c₂' * Λ e t ^ A₂ * NumberField.AdelicHeight.adelicHeight L z ^ B₂) *
              (c₃' * Λ e t ^ A₃ * (NumberField.AdelicHeight.adelicHeight L z)⁻¹ ^ B₂) :=
            mul_le_mul hEi hEj (norm_nonneg _)
              (mul_nonneg (mul_nonneg hc₂'0 (hΛpow0 e t A₂)) (pow_nonneg hHz.le _))
        _ = c₂' * c₃' * Λ e t ^ (A₂ + A₃) *
              (NumberField.AdelicHeight.adelicHeight L z *
                (NumberField.AdelicHeight.adelicHeight L z)⁻¹) ^ B₂ := by
            rw [mul_pow]; ring
        _ = c₂' * c₃' * Λ e t ^ (A₂ + A₃) := by
            rw [mul_inv_cancel₀ hHz.ne', one_pow, mul_one]
        _ ≤ CR * Λ e t ^ (A₂ + A₂ + A₃) := by
            refine mul_le_mul ?_ (pow_le_pow_right₀ (hΛ1 e t) (by omega)) (hΛpow0 e t _) hCR0
            exact le_add_of_nonneg_left (mul_nonneg (pow_nonneg hc₂'0 2) (pow_nonneg (Real.exp_pos R).le _))
    ·
      have hle : NumberField.AdelicHeight.adelicHeight L z ≤ Real.exp R := not_lt.1 hcut
      have hle' : NumberField.AdelicHeight.adelicHeight L z' ≤ Real.exp R := by rw [hzz]; exact hle
      have hEj := hΛE e j t z' hz' hle'
      have hHB : NumberField.AdelicHeight.adelicHeight L z ^ B₂ ≤ Real.exp R ^ B₂ :=
        pow_le_pow_left₀ hHz.le hle _
      calc ‖EE e i ((t : ℂ) * Complex.I) z‖ * _
          ≤ (c₂' * Λ e t ^ A₂ * NumberField.AdelicHeight.adelicHeight L z ^ B₂) *
              (c₂' * Λ e t ^ A₂ * Real.exp R ^ B₂) :=
            mul_le_mul hEi hEj (norm_nonneg _)
              (mul_nonneg (mul_nonneg hc₂'0 (hΛpow0 e t A₂)) (pow_nonneg hHz.le _))
        _ ≤ (c₂' * Λ e t ^ A₂ * Real.exp R ^ B₂) * (c₂' * Λ e t ^ A₂ * Real.exp R ^ B₂) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHB (mul_nonneg hc₂'0 (hΛpow0 e t A₂)))
              (mul_nonneg (mul_nonneg hc₂'0 (hΛpow0 e t A₂)) (pow_nonneg (Real.exp_pos R).le _))
        _ = c₂' ^ 2 * Real.exp R ^ (B₂ + B₂) * Λ e t ^ (A₂ + A₂) := by ring
        _ ≤ CR * Λ e t ^ (A₂ + A₂ + A₃) := by
            refine mul_le_mul ?_ (pow_le_pow_right₀ (hΛ1 e t) (by omega)) (hΛpow0 e t _) hCR0
            exact le_add_of_nonneg_right (mul_nonneg hc₂'0 hc₃'0)

  have hprod2 : ∀ (e : ιE) (i j : Fin (nE e)) (t : ℝ) (z z' : AdelicGL2 (𝓞 L) L),
      NumberField.AdelicHeight.adelicHeight L z' = NumberField.AdelicHeight.adelicHeight L z →
      h₀ ≤ NumberField.AdelicHeight.adelicHeight L z →
        ‖(@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (EE e i ((t : ℂ) * Complex.I))) z‖ *
          ‖(@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (EE e j ((t : ℂ) * Complex.I))) z'‖ ≤ CR2 * Λ e t ^ (A₂ + A₂ + A₃ + A₃) := by
    intro e i j t z z' hzz hz
    have hHz := hHpos z
    have hz' : h₀ ≤ NumberField.AdelicHeight.adelicHeight L z' := by rw [hzz]; exact hz
    by_cases hcut : Real.exp R < NumberField.AdelicHeight.adelicHeight L z
    ·
      have hcut' : Real.exp R < NumberField.AdelicHeight.adelicHeight L z' := by rw [hzz]; exact hcut
      have hEi := hΛD e i t z hz hcut
      have hEj := hΛD e j t z' hz' hcut'
      rw [hzz] at hEj
      have hinv : (NumberField.AdelicHeight.adelicHeight L z)⁻¹ ^ B₂ ≤ h₀⁻¹ ^ B₂ :=
        pow_le_pow_left₀ (inv_nonneg.2 hHz.le) (inv_anti₀ hh₀ hz) _
      have hinv0 : 0 ≤ (NumberField.AdelicHeight.adelicHeight L z)⁻¹ ^ B₂ := pow_nonneg (inv_nonneg.2 hHz.le) _
      calc _ ≤ (c₃' * Λ e t ^ A₃ * (NumberField.AdelicHeight.adelicHeight L z)⁻¹ ^ B₂) *
              (c₃' * Λ e t ^ A₃ * (NumberField.AdelicHeight.adelicHeight L z)⁻¹ ^ B₂) :=
            mul_le_mul hEi hEj (norm_nonneg _)
              (mul_nonneg (mul_nonneg hc₃'0 (hΛpow0 e t A₃)) hinv0)
        _ ≤ (c₃' * Λ e t ^ A₃ * h₀⁻¹ ^ B₂) * (c₃' * Λ e t ^ A₃ * h₀⁻¹ ^ B₂) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hinv (mul_nonneg hc₃'0 (hΛpow0 e t A₃)))
              (mul_le_mul_of_nonneg_left hinv (mul_nonneg hc₃'0 (hΛpow0 e t A₃)))
              (mul_nonneg (mul_nonneg hc₃'0 (hΛpow0 e t A₃)) hinv0)
              (mul_nonneg (mul_nonneg hc₃'0 (hΛpow0 e t A₃)) (pow_nonneg (inv_nonneg.2 hh₀.le) _))
        _ = c₃' ^ 2 * h₀⁻¹ ^ (B₂ + B₂) * Λ e t ^ (A₃ + A₃) := by ring
        _ ≤ CR2 * Λ e t ^ (A₂ + A₂ + A₃ + A₃) := by
            refine mul_le_mul ?_ (pow_le_pow_right₀ (hΛ1 e t) (by omega)) (hΛpow0 e t _) hCR20
            exact le_add_of_nonneg_left (mul_nonneg (pow_nonneg hc₂'0 2) (pow_nonneg (Real.exp_pos R).le _))
    ·
      have hle : NumberField.AdelicHeight.adelicHeight L z ≤ Real.exp R := not_lt.1 hcut
      have hle' : NumberField.AdelicHeight.adelicHeight L z' ≤ Real.exp R := by rw [hzz]; exact hle
      have hEi := hΛE e i t z hz hle
      have hEj := hΛE e j t z' hz' hle'
      calc _ ≤ (c₂' * Λ e t ^ A₂ * Real.exp R ^ B₂) * (c₂' * Λ e t ^ A₂ * Real.exp R ^ B₂) :=
            mul_le_mul hEi hEj (norm_nonneg _)
              (mul_nonneg (mul_nonneg hc₂'0 (hΛpow0 e t A₂)) (pow_nonneg (Real.exp_pos R).le _))
        _ = c₂' ^ 2 * Real.exp R ^ (B₂ + B₂) * Λ e t ^ (A₂ + A₂) := by ring
        _ ≤ CR2 * Λ e t ^ (A₂ + A₂ + A₃ + A₃) := by
            refine mul_le_mul ?_ (pow_le_pow_right₀ (hΛ1 e t) (by omega)) (hΛpow0 e t _) hCR20
            exact le_add_of_nonneg_right
              (mul_nonneg (pow_nonneg hc₃'0 2) (pow_nonneg (inv_nonneg.2 hh₀.le) _))

  have h1' : ∀ (e : ιE) (t : ℝ),
      (∑ i : Fin (nE e), ∑ j : Fin (nE e),
        ‖∫ k, rightConv L (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
            conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)‖) ≤
        c₁' * Λ e t ^ (-((M₀ + (A₂ + A₂ + A₃) : ℕ) : ℝ)) := by
    intro e t
    refine (h1 e t).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (R4DomSigma.rpow_neg_natCast_nonneg (hΛ1 e t) _)

  set Gf : ιE → ℝ → ℝ := fun e t =>
    c₁' * CR * (if nE e = 0 then 0 else Λ e t ^ (-(M₀ : ℝ))) with hGfdef
  have hGf0 : ∀ e t, 0 ≤ Gf e t := by
    intro e t
    simp only [hGfdef]
    split_ifs
    · simp
    · exact mul_nonneg (mul_nonneg hc₁'0 hCR0) (R4DomSigma.rpow_neg_natCast_nonneg (hΛ1 e t) _)
  have hGfint : ∀ e, Integrable (Gf e) := by
    intro e
    by_cases he : nE e = 0
    · have : Gf e = fun _ => 0 := by funext t; simp [hGfdef, he]
      rw [this]
      exact integrable_zero _ _ _
    · have : Gf e = fun t => c₁' * CR * Λ e t ^ (-(M₀ : ℝ)) := by funext t; simp [hGfdef, he]
      rw [this]
      exact (hΛint' e).const_mul _
  have hGfI : ∀ e, ∫ t, Gf e t = c₁' * CR * (if nE e = 0 then (0 : ℝ) else ∫ t : ℝ, Λ e t ^ (-(M₀ : ℝ))) := by
    intro e
    simp only [hGfdef]
    rw [integral_const_mul]
    split_ifs <;> simp

  have hF : ∀ (e : ιE) (p : ℝ × AdelicGL2 (𝓞 L) L),
      h₀ ≤ NumberField.AdelicHeight.adelicHeight L p.2 →
        ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
        (∫ k, rightConv L (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
            conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) *
          (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
            conj ((@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => EE e j ((p.1 : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
              p.2)))‖ ≤ Gf e p.1 := by
    intro e p hp
    by_cases he : nE e = 0
    · rw [hempty e he]
      simp [hGfdef, he]
    · have hP : ∀ i j : Fin (nE e), ‖EE e i ((p.1 : ℂ) * Complex.I) p.2‖ *
          ‖(@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => EE e j ((p.1 : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y)) p.2)‖ ≤
            CR * Λ e p.1 ^ (A₂ + A₂ + A₃) := by
        intro i j
        rw [hΛσ e j p.1 (Real.exp R) p.2]
        exact hprod e i j p.1 p.2 _ (hHσ p.2) hp
      refine (R4DomSigma.norm_sum_sum_mul_le _ _ _ hP).trans ?_
      have hkey := R4DomSigma.rpow_neg_add_mul_pow (hΛ1 e p.1) M₀ (A₂ + A₂ + A₃)
      calc _ ≤ c₁' * Λ e p.1 ^ (-((M₀ + (A₂ + A₂ + A₃) : ℕ) : ℝ)) * (CR * Λ e p.1 ^ (A₂ + A₂ + A₃)) :=
            mul_le_mul_of_nonneg_right (h1' e p.1) (mul_nonneg hCR0 (hΛpow0 e p.1 _))
        _ = c₁' * CR * (Λ e p.1 ^ (-((M₀ + (A₂ + A₂ + A₃) : ℕ) : ℝ)) * Λ e p.1 ^ (A₂ + A₂ + A₃)) := by
            ring
        _ = Gf e p.1 := by rw [hkey]; simp [hGfdef, he]

  have hEcont : ∀ (e : ιE) (i : Fin (nE e)),
      Continuous fun p : ℝ × AdelicGL2 (𝓞 L) L => EE e i ((p.1 : ℂ) * Complex.I) p.2 := by
    intro e i
    obtain ⟨-, -, hax, -, -, -, hEjc, -⟩ := hEE e i
    have hmap : Continuous fun p : ℝ × AdelicGL2 (𝓞 L) L => (((p.1 : ℂ) * Complex.I), p.2) :=
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).prodMk continuous_snd
    exact hEjc.comp_continuous hmap fun p => ⟨hax (by simp), Set.mem_univ _⟩

  have hLmeas0 : ∀ (e : ιE) (j : Fin (nE e)), Measurable fun p : ℝ × AdelicGL2 (𝓞 L) L =>
      (@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
        (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
        (EE e j ((p.1 : ℂ) * Complex.I))) p.2 := fun e j =>
    R4DomSigma.measurable_lambdaT_family L (fun t => EE e j ((t : ℂ) * Complex.I)) (hEcont e j) ΦL _ _
      (Real.exp R)
  have hLmeas : ∀ (e : ιE) (j : Fin (nE e)), Measurable fun p : ℝ × AdelicGL2 (𝓞 L) L =>
      (@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
        (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
        (fun y => EE e j ((p.1 : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))) p.2 := by
    intro e j
    have hfun : (fun p : ℝ × AdelicGL2 (𝓞 L) L =>
        (@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (fun y => EE e j ((p.1 : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))) p.2) =
        (fun p : ℝ × AdelicGL2 (𝓞 L) L =>
          (@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (EE e j ((p.1 : ℂ) * Complex.I))) p.2) ∘
          (fun p : ℝ × AdelicGL2 (𝓞 L) L => (p.1, AutomorphicForm.sigmaAdelicAct K L D σ.symm p.2)) := by
      funext p
      exact hΛσ e j p.1 (Real.exp R) p.2
    rw [hfun]
    exact (hLmeas0 e j).comp
      (measurable_fst.prodMk
        ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ.symm).measurable.comp measurable_snd))

  have hmeas : ∀ e : ιE, Measurable fun p : ℝ × AdelicGL2 (𝓞 L) L =>
      ∑ i : Fin (nE e), ∑ j : Fin (nE e),
        (∫ k, rightConv L (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
            conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) *
          (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
            conj ((@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => EE e j ((p.1 : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
              p.2))) := by
    intro e
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    refine Measurable.mul ((hacont e i j).measurable.comp measurable_fst) ?_
    refine Measurable.mul (hEcont e i).measurable ?_
    exact (Complex.continuous_conj.measurable).comp (hLmeas e j)

  have hvol := R4DomSigma.measure_lt_top_of_isFundamentalDomain_slab L hα hαβ Φ₀ hΦ₀s hΦ₀
  haveI hfin : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hvol⟩
  have hae1 := R4DomSigma.ae_mem_of_isFundamentalDomain_slab L Φ₀ hΦ₀s hΦ₀
  have hae2 : ∀ᵐ p : ℝ × AdelicGL2 (𝓞 L) L ∂((volume : Measure ℝ).prod
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀)), p.2 ∈ Φ₀ :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
      (ν := (adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀)).ae hae1
  have hbound : ∀ e : ιE, ∀ᵐ p : ℝ × AdelicGL2 (𝓞 L) L ∂((volume : Measure ℝ).prod
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀)),
        ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
        (∫ k, rightConv L (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
            conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) *
          (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
            conj ((@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => EE e j ((p.1 : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
              p.2)))‖ ≤ Gf e p.1 := by
    intro e
    filter_upwards [hae2] with p hp using hF e p (hfloor _ hp)
  have hint : ∀ e : ιE, Integrable (fun p : ℝ × AdelicGL2 (𝓞 L) L =>
      ∑ i : Fin (nE e), ∑ j : Fin (nE e),
        (∫ k, rightConv L (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
            conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) *
          (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
            conj ((@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => EE e j ((p.1 : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
              p.2))))
      ((volume : Measure ℝ).prod ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀)) := by
    intro e
    exact Integrable.mono' ((hGfint e).comp_fst _) (hmeas e).aestronglyMeasurable (hbound e)

  have hsum : Summable fun e : ιE => ∫ p : ℝ × AdelicGL2 (𝓞 L) L, ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
        (∫ k, rightConv L (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) *
            conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) *
          (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
            conj ((@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => EE e j ((p.1 : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
              p.2)))‖
        ∂((volume : Measure ℝ).prod ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀)) := by
    have hV0 : 0 ≤ (((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀).real Set.univ) := measureReal_nonneg
    refine Summable.of_nonneg_of_le (fun e => integral_nonneg fun _ => norm_nonneg _) (fun e => ?_)
      ((hΛsum'.mul_left (c₁' * CR)).mul_left
        (((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀).real Set.univ))
    calc _ ≤ ∫ p : ℝ × AdelicGL2 (𝓞 L) L, Gf e p.1 ∂((volume : Measure ℝ).prod
            ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((hGfint e).comp_fst _) (hbound e)
      _ = (((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀).real Set.univ) • ∫ t, Gf e t :=
          integral_fun_fst _
      _ = _ := by rw [hGfI e, smul_eq_mul]
  refine ⟨hint, hsum, fun e i j t => ⟨?_, ?_⟩⟩

  · have hm : Measurable fun x : AdelicGL2 (𝓞 L) L =>
        (@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y)) x) *
          conj (EE e i ((t : ℂ) * Complex.I) x) :=
      ((hLmeas e j).comp (measurable_const.prodMk measurable_id)).mul
        (Complex.continuous_conj.measurable.comp
          ((hEcont e i).measurable.comp (measurable_const.prodMk measurable_id)))
    have hbd : ∀ᵐ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀,
        ‖(@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y)) x) *
          conj (EE e i ((t : ℂ) * Complex.I) x)‖ ≤ CR * Λ e t ^ (A₂ + A₂ + A₃) := by
      filter_upwards [hae1] with x hx
      rw [norm_mul, Complex.norm_conj, mul_comm, hΛσ e j t (Real.exp R) x]
      exact hprod e i j t x _ (hHσ x) (hfloor x hx)
    exact Integrable.mono' (integrable_const _) hm.aestronglyMeasurable hbd

  · have hm : Measurable fun x : AdelicGL2 (𝓞 L) L =>
        (@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y)) x) *
          conj ((@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (EE e i ((t : ℂ) * Complex.I))) x) :=
      ((hLmeas e j).comp (measurable_const.prodMk measurable_id)).mul
        (Complex.continuous_conj.measurable.comp
          ((hLmeas0 e i).comp (measurable_const.prodMk measurable_id)))
    have hbd : ∀ᵐ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀,
        ‖(@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y)) x) *
          conj ((@AutomorphicForm.lambdaT _ pins.nS _ _ pins.ν (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (EE e i ((t : ℂ) * Complex.I))) x)‖ ≤ CR2 * Λ e t ^ (A₂ + A₂ + A₃ + A₃) := by
      filter_upwards [hae1] with x hx
      rw [norm_mul, Complex.norm_conj, mul_comm, hΛσ e j t (Real.exp R) x]
      exact hprod2 e i j t x _ (hHσ x) (hfloor x hx)
    exact Integrable.mono' (integrable_const _) hm.aestronglyMeasurable hbd

end S_AutomorphicForm_exists_forall_integrable_prod_sum_rightConv_mul_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_symm_of_subset_iUnion_image_centreCutSiegelSet
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_integrable_prod_sum_rightConv_mul_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_symm_of_subset_iUnion_image_centreCutSiegelSet (solution)
