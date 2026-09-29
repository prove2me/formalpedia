-- Prove2me | solution 1 for AutomorphicForm.exists_summable_dominant_rightConv_axis_family_sigma_maassSelberg_pairings_of_isSemiLocalFactorization_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b6281487-473b-5131-885a-4911d0fadfd1

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_TwistedNormClasses
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.DedekindDomain.Factorization
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2
import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight
import Theorems.Thm_MeasureTheory_integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le
import Theorems.Thm_AutomorphicForm_sigmaAdelicAct_mem_adelicMaximalCompact_and_integral_maximalCompactHaar_comp_sigmaAdelicAct
import Theorems.Thm_AutomorphicForm_eq_zero_of_isInducedSection_of_isArchKFinite_of_forall_mem_span_range_of_principalLevel_bot
import Theorems.Thm_AutomorphicForm_integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_NumberField_TateGlobal_exists_isHaarMeasure_isFundamentalDomain_measure_inter_shell_ne_zero_ne_top
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_summable_dominant_rightConv_axis_family_sigma_maassSelberg_pairings_of_isSemiLocalFactorization_lipschitz
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false

noncomputable section

namespace R4RegSigmaReduce2

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open Set Metric Filter
open scoped ComplexConjugate Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section OnK

variable (L : Type) [Field L] [NumberField L]

theorem continuous_axis : Continuous fun t : ℝ => (t : ℂ) * Complex.I :=
  Complex.continuous_ofReal.mul continuous_const

theorem axis_mem {O : Set ℂ} (hO : {s : ℂ | s.re = 0} ⊆ O) (t : ℝ) : (t : ℂ) * Complex.I ∈ O :=
  hO (by simp [Complex.mul_re])

theorem continuousOn_deriv_param {X : Type*} [TopologicalSpace X] (N : ℂ → X → ℂ) (O : Set ℂ)
    (hO : IsOpen O) (hN : ContinuousOn (fun p : ℂ × X => N p.1 p.2) (O ×ˢ univ))
    (hNa : ∀ x : X, AnalyticOnNhd ℂ (fun s => N s x) O) :
    ContinuousOn (fun p : ℂ × X => deriv (fun s => N s p.2) p.1) (O ×ˢ univ) := by
  rintro ⟨s₀, x₀⟩ ⟨hs₀, -⟩
  obtain ⟨R, hR, hRO⟩ := Metric.isOpen_iff.mp hO s₀ hs₀
  set r : ℝ := R / 3 with hr_def
  have hr : 0 < r := by positivity
  have h2r : closedBall s₀ (2 * r) ⊆ O :=
    (closedBall_subset_ball (by rw [hr_def]; linarith)).trans hRO
  have hdiff : ∀ x : X, DifferentiableOn ℂ (fun s => N s x) O := fun x =>
    (hNa x).analyticOn.differentiableOn
  have hd : ContinuousAt (deriv fun s => N s x₀) s₀ := ((hNa x₀).deriv s₀ hs₀).continuousAt
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hcont : ContinuousOn (Function.uncurry fun (x : X) (s : ℂ) => N s x)
      (univ ×ˢ closedBall s₀ (2 * r)) := by
    have hsw : Continuous fun p : X × ℂ => ((p.2, p.1) : ℂ × X) := by fun_prop
    refine (hN.comp hsw.continuousOn ?_)
    rintro ⟨x, s⟩ ⟨-, hs⟩
    exact ⟨h2r hs, mem_univ _⟩
  have hεr : 0 < ε / 2 * r := by positivity
  obtain ⟨v, hv, hvN⟩ := IsCompact.mem_uniformity_of_prod (isCompact_closedBall s₀ (2 * r)) hcont
    (mem_univ x₀) (Metric.dist_mem_uniformity hεr)
  rw [nhdsWithin_univ] at hv
  have hd' : ∀ᶠ s in 𝓝 s₀, dist (deriv (fun s => N s x₀) s) (deriv (fun s => N s x₀) s₀) < ε / 2 :=
    Metric.tendsto_nhds.mp hd (ε / 2) (by positivity)
  have hball : ∀ᶠ s in 𝓝 s₀, s ∈ ball s₀ r := ball_mem_nhds s₀ hr
  have hprod : ∀ᶠ p in 𝓝[O ×ˢ univ] ((s₀, x₀) : ℂ × X),
      (p.1 ∈ ball s₀ r ∧ dist (deriv (fun s => N s x₀) p.1) (deriv (fun s => N s x₀) s₀) < ε / 2) ∧
        p.2 ∈ v := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    rw [nhds_prod_eq]
    exact Filter.Eventually.prod_mk (hball.and hd') hv
  filter_upwards [hprod] with p hp
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
  set s := p.1
  set x := p.2
  have hsub : closedBall s r ⊆ closedBall s₀ (2 * r) := by
    refine closedBall_subset_closedBall' ?_
    have : dist s s₀ < r := mem_ball.mp hp1
    linarith
  have hsO : closedBall s r ⊆ O := hsub.trans h2r
  have hds : deriv (fun s => N s x) s = Complex.cderiv r (fun s => N s x) s :=
    (Complex.cderiv_eq_deriv hO (hdiff x) hr hsO).symm
  have hds₀ : deriv (fun s => N s x₀) s = Complex.cderiv r (fun s => N s x₀) s :=
    (Complex.cderiv_eq_deriv hO (hdiff x₀) hr hsO).symm
  have hsphere : ∀ w ∈ sphere s r, ‖N w x - N w x₀‖ < ε / 2 * r := by
    intro w hw
    have hw' : w ∈ closedBall s₀ (2 * r) := hsub (sphere_subset_closedBall hw)
    have := hvN x hp3 w hw'
    rwa [Set.mem_setOf_eq, dist_eq_norm] at this
  have hcx : ContinuousOn (fun s => N s x) (sphere s r) :=
    (hdiff x).continuousOn.mono ((sphere_subset_closedBall).trans hsO)
  have hcx₀ : ContinuousOn (fun s => N s x₀) (sphere s r) :=
    (hdiff x₀).continuousOn.mono ((sphere_subset_closedBall).trans hsO)
  have h1 : ‖deriv (fun s => N s x) s - deriv (fun s => N s x₀) s‖ < ε / 2 := by
    rw [hds, hds₀]
    have := Complex.norm_cderiv_sub_lt hr hsphere hcx hcx₀
    rwa [mul_div_assoc, div_self hr.ne', mul_one] at this
  have h2 : ‖deriv (fun s => N s x₀) s - deriv (fun s => N s x₀) s₀‖ < ε / 2 := by
    rw [← dist_eq_norm]; exact hp2
  show dist (deriv (fun s => N s x) s) (deriv (fun s => N s x₀) s₀) < ε
  rw [dist_eq_norm]
  calc ‖deriv (fun s => N s x) s - deriv (fun s => N s x₀) s₀‖
      = ‖(deriv (fun s => N s x) s - deriv (fun s => N s x₀) s) +
          (deriv (fun s => N s x₀) s - deriv (fun s => N s x₀) s₀)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖deriv (fun s => N s x) s - deriv (fun s => N s x₀) s‖ +
          ‖deriv (fun s => N s x₀) s - deriv (fun s => N s x₀) s₀‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

theorem continuous_axis_coe (θ : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L) (hθ : Continuous θ) :
    Continuous fun p : ℝ × adelicMaximalCompact L =>
      (((p.1 : ℂ) * Complex.I, θ (p.2 : AdelicGL2 (𝓞 L) L)) : ℂ × AdelicGL2 (𝓞 L) L) :=
  ((continuous_axis).comp continuous_fst).prodMk (hθ.comp (continuous_subtype_val.comp continuous_snd))

theorem continuous_eval_axis {O : Set ℂ} (hO : {s : ℂ | s.re = 0} ⊆ O)
    (M : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
    (hM : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => M p.1 p.2) (O ×ˢ univ))
    (θ : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L) (hθ : Continuous θ) :
    Continuous fun p : ℝ × adelicMaximalCompact L =>
      M ((p.1 : ℂ) * Complex.I) (θ (p.2 : AdelicGL2 (𝓞 L) L)) :=
  hM.comp_continuous (continuous_axis_coe L θ hθ) (fun p => ⟨axis_mem hO p.1, mem_univ _⟩)

theorem continuous_deriv_eval_axis {O : Set ℂ} (hOo : IsOpen O) (hO : {s : ℂ | s.re = 0} ⊆ O)
    (M : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
    (hM : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => M p.1 p.2) (O ×ˢ univ))
    (hMa : ∀ g, AnalyticOnNhd ℂ (fun s => M s g) O)
    (θ : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L) (hθ : Continuous θ) :
    Continuous fun p : ℝ × adelicMaximalCompact L =>
      deriv (fun s => M s (θ (p.2 : AdelicGL2 (𝓞 L) L))) ((p.1 : ℂ) * Complex.I) :=
  (continuousOn_deriv_param M O hOo hM hMa).comp_continuous (continuous_axis_coe L θ hθ)
    (fun p => ⟨axis_mem hO p.1, mem_univ _⟩)

theorem continuous_integral_K {F : ℝ → adelicMaximalCompact L → ℂ}
    (hF : Continuous (fun p : ℝ × adelicMaximalCompact L => F p.1 p.2)) :
    Continuous (fun t : ℝ => ∫ k, F t k ∂(maximalCompactHaar L)) := by
  have h := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar L) (f := F)
    (show Continuous (Function.uncurry F) from hF) isCompact_univ
  simpa only [Measure.restrict_univ] using h

theorem memLp_two_of_continuous (x : adelicMaximalCompact L → ℂ) (hx : Continuous x) :
    MemLp x (ENNReal.ofReal 2) (maximalCompactHaar L) := by
  obtain ⟨C, hC⟩ := (isCompact_range hx).isBounded.exists_norm_le
  exact MemLp.of_bound hx.aestronglyMeasurable C (Eventually.of_forall fun k => hC _ ⟨k, rfl⟩)

theorem integrable_of_continuous_K (x : adelicMaximalCompact L → ℂ) (hx : Continuous x) :
    Integrable x (maximalCompactHaar L) := by
  obtain ⟨C, hC⟩ := (isCompact_range hx).isBounded.exists_norm_le
  exact Integrable.of_bound  hx.aestronglyMeasurable C (Eventually.of_forall fun k => hC _ ⟨k, rfl⟩)

theorem norm_integral_mul_conj_le (x y : adelicMaximalCompact L → ℂ) (hx : Continuous x) (hy : Continuous y) :
    ‖∫ k, x k * conj (y k) ∂(maximalCompactHaar L)‖ ≤
      Real.sqrt (∫ k, ‖x k‖ ^ 2 ∂(maximalCompactHaar L)) * Real.sqrt (∫ k, ‖y k‖ ^ 2 ∂(maximalCompactHaar L)) := by
  calc ‖∫ k, x k * conj (y k) ∂(maximalCompactHaar L)‖
      ≤ ∫ k, ‖x k * conj (y k)‖ ∂(maximalCompactHaar L) := norm_integral_le_integral_norm _
    _ = ∫ k, ‖x k‖ * ‖y k‖ ∂(maximalCompactHaar L) := by
        refine integral_congr_ae (Eventually.of_forall fun k => ?_)
        simp only [norm_mul, Complex.norm_conj]
    _ ≤ (∫ k, ‖x k‖ ^ (2 : ℝ) ∂(maximalCompactHaar L)) ^ (1 / (2 : ℝ)) *
          (∫ k, ‖y k‖ ^ (2 : ℝ) ∂(maximalCompactHaar L)) ^ (1 / (2 : ℝ)) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
          (memLp_two_of_continuous L x hx) (memLp_two_of_continuous L y hy)
    _ = Real.sqrt (∫ k, ‖x k‖ ^ 2 ∂(maximalCompactHaar L)) *
          Real.sqrt (∫ k, ‖y k‖ ^ 2 ∂(maximalCompactHaar L)) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        congr 2 <;> refine integral_congr_ae (Eventually.of_forall fun k => ?_) <;>
          simp only [Real.rpow_two]

theorem integral_mul_conj_self (x : adelicMaximalCompact L → ℂ) :
    (∫ k, x k * conj (x k) ∂(maximalCompactHaar L)) =
      ((∫ k, ‖x k‖ ^ 2 ∂(maximalCompactHaar L) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [Complex.mul_conj', Complex.ofReal_pow]

theorem integral_mul_conj_sub (x y y' : adelicMaximalCompact L → ℂ) (hx : Continuous x) (hy : Continuous y)
    (hy' : Continuous y') :
    (∫ k, x k * conj (y k) ∂(maximalCompactHaar L)) - (∫ k, x k * conj (y' k) ∂(maximalCompactHaar L)) =
      ∫ k, x k * conj (y k - y' k) ∂(maximalCompactHaar L) := by
  rw [← integral_sub (integrable_of_continuous_K L (fun k => x k * conj (y k)) (hx.mul hy.star))
    (integrable_of_continuous_K L (fun k => x k * conj (y' k)) (hx.mul hy'.star))]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [map_sub, mul_sub]

theorem integral_mul_conj_sub' (x x' y : adelicMaximalCompact L → ℂ) (hx : Continuous x) (hx' : Continuous x')
    (hy : Continuous y) :
    (∫ k, x k * conj (y k) ∂(maximalCompactHaar L)) - (∫ k, x' k * conj (y k) ∂(maximalCompactHaar L)) =
      ∫ k, (x k - x' k) * conj (y k) ∂(maximalCompactHaar L) := by
  rw [← integral_sub (integrable_of_continuous_K L (fun k => x k * conj (y k)) (hx.mul hy.star))
    (integrable_of_continuous_K L (fun k => x' k * conj (y k)) (hx'.mul hy.star))]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [sub_mul]

theorem lipschitz_on_K (Nf : ℂ → AdelicGL2 (𝓞 L) L → ℂ) (O : Set ℂ) (hOo : IsOpen O)
    (hO : {s : ℂ | s.re = 0} ⊆ O)
    (hNa : ∀ g, AnalyticOnNhd ℂ (fun s => Nf s g) O)
    (hNc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nf p.1 p.2) (O ×ˢ univ))
    (θ : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L) (hθ : Continuous θ) (c : ℂ) (t t' B : ℝ)
    (hB : ∀ τ ∈ Set.uIcc t t',
      ∫ k, ‖c * deriv (fun s : ℂ => Nf s (θ (k : AdelicGL2 (𝓞 L) L))) ((τ : ℂ) * Complex.I)‖ ^ 2
        ∂(maximalCompactHaar L) ≤ B ^ 2) :
    ∫ k, ‖c * Nf ((t : ℂ) * Complex.I) (θ (k : AdelicGL2 (𝓞 L) L)) -
        c * Nf ((t' : ℂ) * Complex.I) (θ (k : AdelicGL2 (𝓞 L) L))‖ ^ 2 ∂(maximalCompactHaar L) ≤
      (B * |t - t'|) ^ 2 := by
  set N : ℂ → adelicMaximalCompact L → ℂ := fun s k => c * Nf s (θ (k : AdelicGL2 (𝓞 L) L)) with hN
  have hNa' : ∀ k : adelicMaximalCompact L, AnalyticOnNhd ℂ (fun s => N s k) O := fun k =>
    fun s hs => analyticAt_const.mul (hNa _ s hs)
  have hNc' : ContinuousOn (fun p : ℂ × adelicMaximalCompact L => N p.1 p.2) (O ×ˢ Set.univ) := by
    have h1 : Continuous fun p : ℂ × adelicMaximalCompact L =>
        ((p.1, θ (p.2 : AdelicGL2 (𝓞 L) L)) : ℂ × AdelicGL2 (𝓞 L) L) :=
      continuous_fst.prodMk (hθ.comp (continuous_subtype_val.comp continuous_snd))
    have h2 : ContinuousOn (fun p : ℂ × adelicMaximalCompact L => Nf p.1 (θ (p.2 : AdelicGL2 (𝓞 L) L)))
        (O ×ˢ Set.univ) := hNc.comp h1.continuousOn (fun p hp => ⟨hp.1, mem_univ _⟩)
    exact continuousOn_const.mul h2
  have hderiv : ∀ (k : adelicMaximalCompact L) (τ : ℝ),
      deriv (fun s => N s k) ((τ : ℂ) * Complex.I) =
        c * deriv (fun s : ℂ => Nf s (θ (k : AdelicGL2 (𝓞 L) L))) ((τ : ℂ) * Complex.I) := by
    intro k τ
    exact deriv_const_mul _ ((hNa _ _ (axis_mem hO τ)).differentiableAt)
  have hB' : ∀ τ ∈ Set.uIcc t t',
      ∫ k, ‖deriv (fun s : ℂ => N s k) ((τ : ℂ) * Complex.I)‖ ^ 2 ∂(maximalCompactHaar L) ≤ B ^ 2 := by
    intro τ hτ
    simp_rw [hderiv]
    exact hB τ hτ
  exact MeasureTheory.integral_norm_sq_axis_sub_le_of_analyticOnNhd_of_forall_integral_norm_sq_deriv_le
    (maximalCompactHaar L) O hOo hO N hNa' hNc' t t' B hB'

theorem ideleNorm_principal (u : Lˣ) :
    NumberField.TateGlobal.ideleNorm L (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom u) = 1 := by
  unfold NumberField.TateGlobal.ideleNorm
  rw [@NumberField.AdeleRing.distribHaarChar_algebraMap L _ _ (adeleBorel (𝓞 L) L)
    (borelSpace_adeleBorel (𝓞 L) L) u]
  simp

end OnK

section Real

theorem rpow_neg_natCast {x : ℝ} (hx : 0 ≤ x) (M : ℕ) : x ^ (-(M : ℝ)) = (x ^ M)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]

variable {ι' : Type*} [Fintype ι'] (a b : ι' → ℝ)

theorem one_le_gauge (t : ℝ) : 1 ≤ 1 + ∑ v, (|t + a v| + |t - b v|) :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem gauge_le_gauge_add (s t : ℝ) :
    (1 + ∑ v, (|s + a v| + |s - b v|)) ≤
      (1 + ∑ v, (|t + a v| + |t - b v|)) + 2 * Fintype.card ι' * |s - t| := by
  have h : ∀ v, |s + a v| + |s - b v| ≤ (|t + a v| + |t - b v|) + 2 * |s - t| := by
    intro v
    have e1 : s + a v = (t + a v) + (s - t) := by ring
    have e2 : s - b v = (t - b v) + (s - t) := by ring
    have h1 : |s + a v| ≤ |t + a v| + |s - t| := by rw [e1]; exact abs_add_le _ _
    have h2 : |s - b v| ≤ |t - b v| + |s - t| := by rw [e2]; exact abs_add_le _ _
    linarith
  calc (1 + ∑ v, (|s + a v| + |s - b v|))
      ≤ 1 + ∑ v, ((|t + a v| + |t - b v|) + 2 * |s - t|) := by
        have hs : (∑ v, (|s + a v| + |s - b v|)) ≤ ∑ v, ((|t + a v| + |t - b v|) + 2 * |s - t|) :=
          Finset.sum_le_sum fun v _ => h v
        linarith
    _ = (1 + ∑ v, (|t + a v| + |t - b v|)) + 2 * Fintype.card ι' * |s - t| := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem gauge_le_mul_gauge {s t : ℝ} (h : |s - t| ≤ 1) :
    (1 + ∑ v, (|s + a v| + |s - b v|)) ≤
      (1 + 2 * Fintype.card ι') * (1 + ∑ v, (|t + a v| + |t - b v|)) := by
  have h1 := gauge_le_gauge_add a b s t
  have h2 := one_le_gauge a b t
  have hr : (0 : ℝ) ≤ 2 * Fintype.card ι' := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hr]

theorem gauge_pow_inv_le {s t : ℝ} (h : |s - t| ≤ 1) (M : ℕ) :
    ((1 + ∑ v, (|t + a v| + |t - b v|)) ^ M)⁻¹ ≤
      (1 + 2 * Fintype.card ι') ^ M * ((1 + ∑ v, (|s + a v| + |s - b v|)) ^ M)⁻¹ := by
  have hs := gauge_le_mul_gauge a b h
  have h1 : (0 : ℝ) < 1 + ∑ v, (|t + a v| + |t - b v|) := lt_of_lt_of_le one_pos (one_le_gauge a b t)
  have h2 : (0 : ℝ) < 1 + ∑ v, (|s + a v| + |s - b v|) := lt_of_lt_of_le one_pos (one_le_gauge a b s)
  have hR : (0 : ℝ) < 1 + 2 * Fintype.card ι' := by positivity
  calc ((1 + ∑ v, (|t + a v| + |t - b v|)) ^ M)⁻¹
      = (1 + 2 * Fintype.card ι') ^ M *
          (((1 + 2 * Fintype.card ι') * (1 + ∑ v, (|t + a v| + |t - b v|))) ^ M)⁻¹ := by
        rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), one_mul]
    _ ≤ (1 + 2 * Fintype.card ι') ^ M * ((1 + ∑ v, (|s + a v| + |s - b v|)) ^ M)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos h2 M) (pow_le_pow_left₀ h2.le hs M)) (pow_nonneg hR.le M)

theorem gauge_le_add_of_mem_uIcc {t t' τ : ℝ} (hτ : τ ∈ uIcc t t') :
    (1 + ∑ v, (|τ + a v| + |τ - b v|)) ≤
      (1 + ∑ v, (|t + a v| + |t - b v|)) + (1 + ∑ v, (|t' + a v| + |t' - b v|)) := by
  have key : ∀ c : ℝ, |τ + c| ≤ |t + c| + |t' + c| := by
    intro c
    rcases mem_uIcc.mp hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases le_or_gt 0 (τ + c) with h | h
      · calc |τ + c| = τ + c := abs_of_nonneg h
          _ ≤ |t' + c| := by rw [abs_eq_self.mpr (by linarith)]; linarith
          _ ≤ |t + c| + |t' + c| := le_add_of_nonneg_left (abs_nonneg _)
      · calc |τ + c| = -(τ + c) := abs_of_neg h
          _ ≤ |t + c| := by rw [abs_eq_neg_self.mpr (by linarith)]; linarith
          _ ≤ |t + c| + |t' + c| := le_add_of_nonneg_right (abs_nonneg _)
    · rcases le_or_gt 0 (τ + c) with h | h
      · calc |τ + c| = τ + c := abs_of_nonneg h
          _ ≤ |t + c| := by rw [abs_eq_self.mpr (by linarith)]; linarith
          _ ≤ |t + c| + |t' + c| := le_add_of_nonneg_right (abs_nonneg _)
      · calc |τ + c| = -(τ + c) := abs_of_neg h
          _ ≤ |t' + c| := by rw [abs_eq_neg_self.mpr (by linarith)]; linarith
          _ ≤ |t + c| + |t' + c| := le_add_of_nonneg_left (abs_nonneg _)
  have hsum : ∑ v, (|τ + a v| + |τ - b v|) ≤
      ∑ v, (|t + a v| + |t - b v|) + ∑ v, (|t' + a v| + |t' - b v|) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have h1 := key (a v)
    have h2 := key (-b v)
    simp only [← sub_eq_add_neg] at h2
    linarith
  linarith

theorem weighted_gauge_le (mμ mν : ι' → ℤ) (M₀ : ℕ)
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
  have h4 := one_le_gauge a b t
  nlinarith

end Real

end R4RegSigmaReduce2

namespace R4RegSigmaReduce2

open MeasureTheory Set Filter
open scoped Topology

section Real2

theorem le_mul_integral_of_local (g : ℝ → ℝ) (hg0 : ∀ s, 0 ≤ g s) (hint : Integrable g) (C : ℝ)
    (hC : 0 ≤ C) (t : ℝ) (h : ∀ s, |s - t| ≤ 1 → g t ≤ C * g s) : g t ≤ C * ∫ s, g s := by
  have hle : t - 1 / 2 ≤ t + 1 / 2 := by linarith
  have h1 : (∫ _ in Set.Icc (t - 1 / 2) (t + 1 / 2), g t) = g t := by
    rw [setIntegral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have h2 : (∫ _ in Set.Icc (t - 1 / 2) (t + 1 / 2), g t) ≤ ∫ s in Set.Icc (t - 1 / 2) (t + 1 / 2), C * g s := by
    refine setIntegral_mono_on (continuous_const.integrableOn_Icc) ((hint.const_mul C).integrableOn)
      measurableSet_Icc fun s hs => h s ?_
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have h3 : (∫ s in Set.Icc (t - 1 / 2) (t + 1 / 2), C * g s) = C * ∫ s in Set.Icc (t - 1 / 2) (t + 1 / 2), g s :=
    integral_const_mul _ _
  have h4 : (∫ s in Set.Icc (t - 1 / 2) (t + 1 / 2), g s) ≤ ∫ s, g s :=
    setIntegral_le_integral hint (Eventually.of_forall hg0)
  calc g t = ∫ _ in Set.Icc (t - 1 / 2) (t + 1 / 2), g t := h1.symm
    _ ≤ C * ∫ s in Set.Icc (t - 1 / 2) (t + 1 / 2), g s := h2.trans h3.le
    _ ≤ C * ∫ s, g s := mul_le_mul_of_nonneg_left h4 hC

theorem sum_norm_sub_le_of_deriv {n : ℕ} (a : Fin n → Fin n → ℝ → ℂ)
    (hd : ∀ i j, Differentiable ℝ (a i j)) (hdc : ∀ i j, Continuous (deriv (a i j)))
    (B : ℝ) {t' t : ℝ} (ht : t' ≤ t) (hB : ∀ s ∈ Set.Icc t' t, (∑ i, ∑ j, ‖deriv (a i j) s‖) ≤ B) :
    (∑ i, ∑ j, ‖a i j t - a i j t'‖) ≤ B * (t - t') := by
  have hftc : ∀ i j, a i j t - a i j t' = ∫ s in t'..t, deriv (a i j) s := fun i j =>
    (intervalIntegral.integral_deriv_eq_sub (fun s _ => hd i j s) ((hdc i j).intervalIntegrable _ _)).symm
  have hii : ∀ i j, IntervalIntegrable (fun s => ‖deriv (a i j) s‖) volume t' t := fun i j =>
    (hdc i j).norm.intervalIntegrable _ _
  calc (∑ i, ∑ j, ‖a i j t - a i j t'‖) = ∑ i, ∑ j, ‖∫ s in t'..t, deriv (a i j) s‖ := by
        simp_rw [hftc]
    _ ≤ ∑ i, ∑ j, ∫ s in t'..t, ‖deriv (a i j) s‖ := by
        gcongr with i _ j _
        exact intervalIntegral.norm_integral_le_integral_norm ht
    _ = ∑ i, ∫ s in t'..t, ∑ j, ‖deriv (a i j) s‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [intervalIntegral.integral_finsetSum fun j _ => hii i j]
    _ = ∫ s in t'..t, ∑ i, ∑ j, ‖deriv (a i j) s‖ := by
        rw [intervalIntegral.integral_finsetSum]
        intro i _
        exact (continuous_finsetSum _ fun j _ => (hdc i j).norm).intervalIntegrable _ _
    _ ≤ ∫ _ in t'..t, B := by
        refine intervalIntegral.integral_mono_on ht ?_ intervalIntegrable_const fun s hs => hB s hs
        exact (continuous_finsetSum _ fun i _ =>
          continuous_finsetSum _ fun j _ => (hdc i j).norm).intervalIntegrable _ _
    _ = B * (t - t') := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

end Real2

end R4RegSigmaReduce2

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

set_option maxHeartbeats 16000000 in
open R4RegSigmaReduce2 Filter in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (N : Ideal (𝓞 L)) (tysL : ArchTypeFamily L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (w : ℝ) (ξ' : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (ιE : Type) [Countable ιE]
      (μE νE : ιE → ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 L) L (μE e)) (_hν : ∀ e, IsUnitaryChar (𝓞 L) L (νE e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 L) L (μE e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 L) L (νE e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μE e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((νE e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 L) L)ˣ),
        ((μE e z : ℂˣ) : ℂ) * ((νE e z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles L,
        μE e z ≠ μE e' z ∨ νE e z ≠ νE e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 L) L (etaFst (μE e) αm hαm s) (etaSnd (νE e) αm hαm s) (φE e j s))
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
        IsInducedSection (𝓞 L) L (etaFst (μE e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (νE e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μE' νE' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 L) L μE' → IsUnitaryChar (𝓞 L) L νE' →
        IsIdeleClassChar (𝓞 L) L μE' → IsIdeleClassChar (𝓞 L) L νE' →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μE' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((νE' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ((μE' z : ℂˣ) : ℂ) * ((νE' z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst μE' αm hαm ((t : ℂ) * Complex.I)) (etaSnd νE' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, μE e z = μE' z ∧ νE e z = νE' z)
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
      (φ₀ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ₀ : Continuous φ₀) (_hφ₀c : HasCompactSupport φ₀)
      (φf₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L S φ₀ φa φf₀ φS →
    let a : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      ∫ k, rightConv L (fun g : AdelicGL2 (𝓞 L) L => φE e j ((t : ℂ) * Complex.I) g *
          (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) φ₀ (k : AdelicGL2 (𝓞 L) L) *
        conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)
    let P : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℂ := fun e i j =>
      ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 L) L) * conj (φE e j 0 (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)
    let Q : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      ∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * NE e i ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => NE e j s g) ((t : ℂ) * Complex.I)) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)
    let U : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      ∫ k, φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)
    let V : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      ∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * NE e i ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (φE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)
    (∀ e i j, Continuous (a e i j)) ∧ (∀ e i j, Continuous (Q e i j)) ∧
    (∀ e i j, Continuous (U e i j)) ∧ (∀ e i j, Continuous (V e i j)) ∧
    (∀ e i j, Integrable (a e i j)) ∧
    (∀ e i j, Integrable (fun t => a e i j t * Q e i j t)) ∧
    (∀ e i j, Integrable (fun t => a e i j t * U e i j t)) ∧
    (∀ e i j, Integrable (fun t => a e i j t * V e i j t)) ∧
    ∃ Lb : ιE → ℝ, Summable Lb ∧
      (∀ e, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
        ∫ t : ℝ, (‖a e i j t‖ * (1 + ‖P e i j‖) + ‖a e i j t * Q e i j t‖ +
          ‖a e i j t * U e i j t‖ + ‖a e i j t * V e i j t‖) ≤ Lb e) ∧
      (∀ (e : ιE) (t : ℝ), ∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖a e i j t‖ * (‖U e i j t‖ + ‖V e i j t‖) ≤ Lb e) ∧
      (∀ (e : ιE) (t t' : ℝ),
        (∑ i : Fin (nE e), ∑ j : Fin (nE e),
          ‖a e i j t * (U e i j t + V e i j t) - a e i j t' * (U e i j t' + V e i j t')‖) ≤ Lb e * |t - t'| ∧
        (∑ i : Fin (nE e), ∑ j : Fin (nE e),
          ‖a e i j t * (U e i j t - V e i j t) - a e i j t' * (U e i j t' - V e i j t')‖) ≤ Lb e * |t - t'|) := by
  intro αm hαm ιE _ μE νE hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat
    hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE φ₀ hφ₀ hφ₀c φf₀ hSL a P Q U V

  rcases eq_or_ne N ⊥ with hNbot | hN
  · subst hNbot
    have hn0 : ∀ e, nE e = 0 := by
      intro e
      by_contra hne
      have hpos : 0 < nE e := Nat.pos_of_ne_zero hne
      set j0 : Fin (nE e) := ⟨0, hpos⟩ with hj0
      have hzero : φE e j0 (((0 : ℝ) : ℂ) * Complex.I) = 0 :=
        AutomorphicForm.eq_zero_of_isInducedSection_of_isArchKFinite_of_forall_mem_span_range_of_principalLevel_bot
          L tysL hαm (μE e) (νE e) (hμ e) (hν e) (hμc e) (hνc e) 0 (nE e)
          (fun j => φE e j (((0 : ℝ) : ℂ) * Complex.I)) (hφEspan e 0)
          (φE e j0 (((0 : ℝ) : ℂ) * Complex.I)) (hφE e j0 _)
          ((hφEjc e j0).comp (continuous_const.prodMk continuous_id)) (hφEK e j0 _) (hφEty e j0 _)
      have hone := hφEon e j0 j0
      rw [if_pos rfl] at hone
      have hint0 : (∫ k, φE e j0 0 (k : AdelicGL2 (𝓞 L) L) * conj (φE e j0 0 (k : AdelicGL2 (𝓞 L) L))
          ∂(maximalCompactHaar L)) = 0 := by
        refine (integral_congr_ae (Eventually.of_forall fun k => ?_)).trans (integral_zero _ _)
        have hk : φE e j0 0 (k : AdelicGL2 (𝓞 L) L) = 0 := by
          rw [← hφEflat e j0 (((0 : ℝ) : ℂ) * Complex.I) k, hzero]; rfl
        simp only [hk, zero_mul]
      rw [hint0] at hone
      exact zero_ne_one hone
    have hE : ∀ e, IsEmpty (Fin (nE e)) := fun e => by rw [hn0 e]; infer_instance
    refine ⟨fun e i => (hE e).elim i, fun e i => (hE e).elim i, fun e i => (hE e).elim i,
      fun e i => (hE e).elim i, fun e i => (hE e).elim i, fun e i => (hE e).elim i,
      fun e i => (hE e).elim i, fun e i => (hE e).elim i, ⟨fun _ => 0, summable_zero, ?_, ?_, ?_⟩⟩
    · intro e; haveI := hE e; simp
    · intro e t; haveI := hE e; simp
    · intro e t t'; haveI := hE e; simp

  rcases isEmpty_or_nonempty ιE with hιE | hιE
  · exact ⟨fun e => hιE.elim e, fun e => hιE.elim e, fun e => hιE.elim e, fun e => hιE.elim e,
      fun e => hιE.elim e, fun e => hιE.elim e, fun e => hιE.elim e, fun e => hιE.elim e,
      ⟨fun _ => 0, summable_zero, fun e => hιE.elim e, fun e => hιE.elim e, fun e => hιE.elim e⟩⟩
  obtain ⟨e₀⟩ := hιE

  classical
  have hσc : Continuous (sigmaAdelicAct K L D σ.symm) := continuous_sigmaAdelicAct K L D σ.symm
  obtain ⟨hKmem, hKint⟩ :=
    AutomorphicForm.sigmaAdelicAct_mem_adelicMaximalCompact_and_integral_maximalCompactHaar_comp_sigmaAdelicAct
      K L D σ.symm

  have hfact : IsFactorizableTestFn L φ₀ := ⟨φa, φf₀, hSL.1, hSL.2.1, hSL.2.2.2.2.2⟩

  have hξ'eq : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) =
      ((μE e₀ z : ℂˣ) : ℂ) * ((νE e₀ z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) :=
    fun z => (hμν e₀ z).symm
  have hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
    have hfun : (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) =
        fun z => ((μE e₀ z : ℂˣ) : ℂ) * ((νE e₀ z : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) := funext hξ'eq
    rw [hfun]
    exact ((hμc e₀).mul (hνc e₀)).mul (Complex.continuous_ofReal.comp
      ((NumberField.TateGlobal.continuous_ideleNorm L).rpow_const fun z =>
        Or.inl (NumberField.TateGlobal.ideleNorm_pos z).ne'))
  have hξw : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ‖((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) := by
    intro z
    rw [hξ'eq, norm_mul, norm_mul, hμ e₀ z, hν e₀ z, one_mul, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos z).le w)]
  have hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξ' ⟨z, Subgroup.mem_top z⟩ = 1 := by
    intro z hz
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hz
    have h1 : μE e₀ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) = 1 := hμic e₀ u
    have h2 : νE e₀ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) = 1 := hνic e₀ u
    have h3 : NumberField.TateGlobal.ideleNorm L
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) = 1 :=
      ideleNorm_principal L u
    apply Units.val_eq_one.mp
    rw [hξ'eq, h1, h2, h3, Units.val_one, Real.one_rpow, Complex.ofReal_one, one_mul, one_mul]

  have hN0 : N ≠ 0 := hN
  set SK : Finset (HeightOneSpectrum (𝓞 L)) := (Ideal.finite_factors hN0).toFinset with hSK
  have hNS : ∀ v : HeightOneSpectrum (𝓞 L), v.asIdeal ∣ N → v ∈ SK := fun v hv =>
    (Set.Finite.mem_toFinset _).mpr hv

  letI mI : MeasurableSpace (AdeleRing (𝓞 L) L)ˣ := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L)ˣ := ⟨rfl⟩
  obtain ⟨νZ, ΩZ, hνZ, hΩZ, -, -⟩ :=
    NumberField.TateGlobal.exists_isHaarMeasure_isFundamentalDomain_measure_inter_shell_ne_zero_ne_top L
  haveI := hνZ
  obtain ⟨TK, cK, hcK, uK, hcov⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet L
  have hcovK := hcov 1 2 two_pos one_le_two

  obtain ⟨D₀, τμ, τν, mμ, mν, M₀, nρ, ρs, B₀, hcard, hτ, hm, hM₀, -, hB⟩ :=
    AutomorphicForm.exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2
      L 1 2 one_pos one_lt_two ∅ cK uK 1 2 TK hcK one_pos one_lt_two hcovK νZ ΩZ hΩZ SK ξ' hξc hξt N hNS tysL
      (fun _ => 0) (fun _ _ => 0) w hξw hαm ιE μE νE hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf
      hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE
  have hτμ : ∀ (e : ιE) (v : InfinitePlace L) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((NumberField.TateGlobal.archLocalChar (μE e) v x : ℂˣ) : ℂ) =
        (((NumberField.TateGlobal.ideleNorm L (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
          (((τμ e v : ℝ) : ℂ) * Complex.I) := fun e v x h1 h2 => (hτ e v x h1 h2).1
  have hτν : ∀ (e : ιE) (v : InfinitePlace L) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((NumberField.TateGlobal.archLocalChar (νE e) v x : ℂˣ) : ℂ) =
        (((NumberField.TateGlobal.ideleNorm L (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
          (((τν e v : ℝ) : ℂ) * Complex.I) := fun e v x h1 h2 => (hτ e v x h1 h2).2
  have hmμ : ∀ (e : ιE) (v : InfinitePlace L) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((NumberField.TateGlobal.archLocalChar (μE e) v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ e v) :=
    fun e v x h1 => (hm e v x h1).1
  have hmν : ∀ (e : ιE) (v : InfinitePlace L) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((NumberField.TateGlobal.archLocalChar (νE e) v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν e v) :=
    fun e v x h1 => (hm e v x h1).2

  obtain ⟨Cs, A, hCs0, hS⟩ :=
    AutomorphicForm.exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight
      L SK ξ' hξc hξt N hNS tysL w hξw

  set M : ℕ := B₀ + A with hMdef
  obtain ⟨Cc, hCc0, hcoef⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn
      L SK ξ' hξc hξt N hNS tysL w hξw φ₀ hφ₀ hφ₀c hfact M

  have hφnorm : ∀ e j (s : ℂ),
      (∫ k, ‖φE e j s (k : AdelicGL2 (𝓞 L) L)‖ ^ 2 ∂(maximalCompactHaar L)) = 1 := by
    intro e j s
    have h1 := hφEon e j j
    rw [if_pos rfl, integral_mul_conj_self] at h1
    have h2 : (∫ k, ‖φE e j 0 (k : AdelicGL2 (𝓞 L) L)‖ ^ 2 ∂(maximalCompactHaar L)) = 1 := by exact_mod_cast h1
    rw [← h2]
    exact integral_congr_ae (Eventually.of_forall fun k => by simp only [hφEflat e j s k])
  have hφn : ∀ e j, (∫ k, ‖φE e j 0 (k : AdelicGL2 (𝓞 L) L)‖ ^ 2 ∂(maximalCompactHaar L)) ≤ 1 :=
    fun e j => (hφnorm e j 0).le

  have hcoef' : ∀ (e : ιE) (i j : Fin (nE e)), ∃ a' : ℝ → ℂ, (∀ t : ℝ, HasDerivAt (a e i j) (a' t) t) ∧
      Continuous a' ∧ ∀ t : ℝ, ‖a e i j t‖ + ‖a' t‖ ≤
        Cc * (1 + ∑ v : InfinitePlace L, (|t + τμ e v| + |t - τν e v|)) ^ (-(M : ℝ)) :=
    fun e i j => hcoef hαm (μE e) (νE e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (hμν e)
      (τμ e) (τν e) (hτμ e) (hτν e) (φE e i) (φE e j) (hφE e i) (hφE e j) (hφEK e i) (hφEK e j)
      (hφEf e i) (hφEf e j) (hφEjc e i) (hφEjc e j) (hφEhol e i) (hφEhol e j) (hφEKu e i) (hφEKu e j)
      (hφEflat e i) (hφEflat e j) (hφElev e i) (hφElev e j) (hφEty e i) (hφEty e j) (hφn e i) (hφn e j)
  choose aD haD haDc hbd using hcoef'
  have hdiffa : ∀ e i j, Differentiable ℝ (a e i j) := fun e i j t => (haD e i j t).differentiableAt
  have hderiv_eq : ∀ e i j, deriv (a e i j) = aD e i j := fun e i j => funext fun t => (haD e i j t).deriv
  have hCderiv : ∀ e i j, Continuous (deriv (a e i j)) := fun e i j => by rw [hderiv_eq]; exact haDc e i j

  let G : ιE → ℝ → ℝ := fun e t => 1 + ∑ v : InfinitePlace L, (|t + τμ e v| + |t - τν e v|)
  have hG1 : ∀ e t, 1 ≤ G e t := fun e t => one_le_gauge (τμ e) (τν e) t
  have hG0 : ∀ e t, 0 < G e t := fun e t => lt_of_lt_of_le one_pos (hG1 e t)
  have hGrw : ∀ (e : ιE) (t : ℝ) (m : ℕ), G e t ^ (-(m : ℝ)) = (G e t ^ m)⁻¹ := fun e t m =>
    rpow_neg_natCast (hG0 e t).le m

  set Pl : ℝ := (Fintype.card (InfinitePlace L) : ℝ) with hPl
  have hPl0 : 0 ≤ Pl := Nat.cast_nonneg _
  set R : ℝ := 1 + 2 * Pl with hRdef
  have hR1 : 1 ≤ R := by rw [hRdef]; linarith
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  set Rm : ℝ := 1 + 2 * Pl * M₀ with hRmdef
  have hRm1 : 1 ≤ Rm := by
    rw [hRmdef]; have h0 : (0:ℝ) ≤ 2 * Pl * (M₀ : ℝ) := by positivity
    linarith
  have hRm0 : 0 ≤ Rm := zero_le_one.trans hRm1
  set d : ℝ := Cs * Rm ^ A with hddef
  have hd0 : 0 ≤ d := mul_nonneg hCs0.le (pow_nonneg hRm0 _)
  set c : ℝ := (D₀ : ℝ) * D₀ * Cc with hcdef
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hCc0.le

  have hcbound : ∀ (e : ιE) (t : ℝ),
      (∑ i, ∑ j, (‖a e i j t‖ + ‖deriv (a e i j) t‖)) ≤ c * (G e t ^ M)⁻¹ := by
    intro e t
    have h1 : ∀ i j : Fin (nE e), ‖a e i j t‖ + ‖deriv (a e i j) t‖ ≤ Cc * (G e t ^ M)⁻¹ := by
      intro i j
      have h := hbd e i j t
      rw [hGrw] at h
      rw [hderiv_eq]
      exact h
    have hcardR : (nE e : ℝ) ≤ D₀ := Nat.cast_le.mpr (hcard e)
    have hx0 : 0 ≤ Cc * (G e t ^ M)⁻¹ := mul_nonneg hCc0.le (inv_nonneg.mpr (pow_nonneg (hG0 e t).le _))
    calc (∑ i, ∑ j, (‖a e i j t‖ + ‖deriv (a e i j) t‖))
        ≤ ∑ _i : Fin (nE e), ∑ _j : Fin (nE e), Cc * (G e t ^ M)⁻¹ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = (nE e : ℝ) * ((nE e : ℝ) * (Cc * (G e t ^ M)⁻¹)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (D₀ : ℝ) * ((D₀ : ℝ) * (Cc * (G e t ^ M)⁻¹)) := by
          have hx1 : 0 ≤ (nE e : ℝ) * (Cc * (G e t ^ M)⁻¹) := mul_nonneg (Nat.cast_nonneg _) hx0
          exact mul_le_mul hcardR (mul_le_mul_of_nonneg_right hcardR hx0) hx1 (Nat.cast_nonneg _)
      _ = c * (G e t ^ M)⁻¹ := by rw [hcdef]; ring

  have hB₀M : B₀ ≤ M := Nat.le_add_right _ _
  have hintM : ∀ e, Integrable (fun t : ℝ => (G e t ^ M)⁻¹) := by
    intro e
    have h := (hB M hB₀M).1 e
    have h' : Integrable (fun t : ℝ => G e t ^ (-(M : ℝ))) := h
    simpa only [hGrw] using h'
  have hintM₀ : ∀ e, Integrable (fun t : ℝ => (G e t ^ B₀)⁻¹) := by
    intro e
    have h := (hB B₀ le_rfl).1 e
    have h' : Integrable (fun t : ℝ => G e t ^ (-(B₀ : ℝ))) := h
    simpa only [hGrw] using h'
  let Bi : ιE → ℝ := fun e => ∫ t : ℝ, (G e t ^ B₀)⁻¹
  have hBi0 : ∀ e, 0 ≤ Bi e := fun e => integral_nonneg fun t => inv_nonneg.mpr (pow_nonneg (hG0 e t).le _)
  have hsumB : Summable fun e => if 0 < nE e then Bi e else (0 : ℝ) := by
    have h := (hB B₀ le_rfl).2.1
    have h' : Summable fun e => if 0 < nE e then ∫ t : ℝ, G e t ^ (-(B₀ : ℝ)) else (0 : ℝ) := h
    simpa only [hGrw] using h'
  have hpowmono : ∀ e t, (G e t ^ M)⁻¹ ≤ (G e t ^ B₀)⁻¹ := fun e t =>
    inv_anti₀ (pow_pos (hG0 e t) _) (pow_le_pow_right₀ (hG1 e t) hB₀M)
  have hGA : ∀ e t, G e t ^ A * (G e t ^ M)⁻¹ = (G e t ^ B₀)⁻¹ := by
    intro e t
    have h0 : G e t ^ A ≠ 0 := pow_ne_zero _ (hG0 e t).ne'
    rw [hMdef, pow_add, mul_inv, mul_comm ((G e t ^ B₀)⁻¹), ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

  have hcmp : ∀ (e : ιE) (m : ℕ) {s t : ℝ}, |s - t| ≤ 1 → (G e t ^ m)⁻¹ ≤ R ^ m * (G e s ^ m)⁻¹ :=
    fun e m s t h => gauge_pow_inv_le (τμ e) (τν e) h m
  have hGcmp : ∀ (e : ιE) {s t : ℝ}, |s - t| ≤ 1 → G e s ≤ R * G e t :=
    fun e s t h => gauge_le_mul_gauge (τμ e) (τν e) h
  have hloc : ∀ e t, (G e t ^ B₀)⁻¹ ≤ R ^ B₀ * Bi e := fun e t =>
    le_mul_integral_of_local (fun s => (G e s ^ B₀)⁻¹) (fun s => inv_nonneg.mpr (pow_nonneg (hG0 e s).le _))
      (hintM₀ e) (R ^ B₀) (pow_nonneg hR0 _) t (fun s hs => hcmp e B₀ hs)
  have hlocM : ∀ e t, (G e t ^ M)⁻¹ ≤ R ^ B₀ * Bi e := fun e t => (hpowmono e t).trans (hloc e t)

  have hXle : ∀ (e : ιE), 0 < nE e → ∀ t : ℝ,
      (1 + ∑ v : InfinitePlace L, (|t + τμ e v| + |t - τν e v| + (|mμ e v| : ℝ) + (|mν e v| : ℝ))) ≤
        Rm * G e t := fun e he t => weighted_gauge_le (τμ e) (τν e) (mμ e) (mν e) M₀ (hM₀ e he) t

  have hax : ∀ e j, {s : ℂ | s.re = 0} ⊆ OE e j := fun e j => (hEE e j).2.2.1
  have hopen : ∀ e j, IsOpen (OE e j) := fun e j => (hEE e j).1
  have hanN : ∀ e j (g : AdelicGL2 (𝓞 L) L), AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j) :=
    fun e j => (hEE e j).2.2.2.2.2.1
  have hcontN : ∀ e j, ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) :=
    fun e j => (hEE e j).2.2.2.2.2.2.2.1

  have hpair : ∀ t : ℝ, Continuous fun k : adelicMaximalCompact L =>
      ((((t : ℂ) * Complex.I), (k : AdelicGL2 (𝓞 L) L)) : ℂ × AdelicGL2 (𝓞 L) L) := fun t =>
    continuous_const.prodMk continuous_subtype_val
  have hpairσ : ∀ t : ℝ, Continuous fun k : adelicMaximalCompact L =>
      ((((t : ℂ) * Complex.I), sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L)) : ℂ × AdelicGL2 (𝓞 L) L) :=
    fun t => continuous_const.prodMk (hσc.comp continuous_subtype_val)
  have hφK : ∀ e j (s : ℂ), Continuous fun k : adelicMaximalCompact L => φE e j s (k : AdelicGL2 (𝓞 L) L) :=
    fun e j s => (hφEjc e j).comp (continuous_const.prodMk continuous_subtype_val)
  have hφKσ : ∀ e j (s : ℂ), Continuous fun k : adelicMaximalCompact L =>
      φE e j s (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L)) :=
    fun e j s => (hφEjc e j).comp (continuous_const.prodMk (hσc.comp continuous_subtype_val))
  have hNK : ∀ e j (t : ℝ), Continuous fun k : adelicMaximalCompact L =>
      ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) :=
    fun e j t => continuous_const.mul ((hcontN e j).comp_continuous (hpair t)
      (fun k => ⟨axis_mem (hax e j) t, Set.mem_univ _⟩))
  have hNKσ : ∀ e j (t : ℝ), Continuous fun k : adelicMaximalCompact L =>
      ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        NE e j ((t : ℂ) * Complex.I) (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L)) :=
    fun e j t => continuous_const.mul ((hcontN e j).comp_continuous (hpairσ t)
      (fun k => ⟨axis_mem (hax e j) t, Set.mem_univ _⟩))
  have hDKσ : ∀ e j (t : ℝ), Continuous fun k : adelicMaximalCompact L =>
      ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        deriv (fun s : ℂ => NE e j s (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ((t : ℂ) * Complex.I) :=
    fun e j t => continuous_const.mul ((continuousOn_deriv_param (NE e j) (OE e j) (hopen e j) (hcontN e j)
      (hanN e j)).comp_continuous (hpairσ t) (fun k => ⟨axis_mem (hax e j) t, Set.mem_univ _⟩))

  have hKsq : ∀ y : AdelicGL2 (𝓞 L) L → ℂ,
      (∫ k, ‖y (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))‖ ^ 2 ∂(maximalCompactHaar L)) =
        ∫ k, ‖y (k : AdelicGL2 (𝓞 L) L)‖ ^ 2 ∂(maximalCompactHaar L) := by
    intro y
    have h := hKint (fun g => (((‖y g‖ ^ 2 : ℝ)) : ℂ))
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    exact_mod_cast h

  have hflatσ : ∀ e j (s : ℂ) (k : adelicMaximalCompact L),
      φE e j s (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L)) =
        φE e j 0 (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L)) :=
    fun e j s k => hφEflat e j s ⟨_, hKmem k⟩

  have hNnorm : ∀ e j (t : ℝ),
      (∫ k, ‖((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
          NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)‖ ^ 2 ∂(maximalCompactHaar L)) = 1 := by
    intro e j t
    have hU :=
      AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
        L hαm (μE e) (νE e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e)
        (φE e j) (hφE e j) (hφEK e j) (hφEf e j) (hφEjc e j) (hφEhol e j) (hφEKu e j)
        (φE e j) (hφE e j) (hφEK e j) (hφEf e j) (hφEjc e j) (hφEhol e j) (hφEKu e j)
        (OE e j) (EE e j) (NE e j) (hEE e j) (OE e j) (EE e j) (NE e j) (hEE e j) t
    have hU' : (∫ k, (((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
          NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) *
        conj (((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
          NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) =
        ∫ k, φE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) *
          conj (φE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L) := hU
    rw [integral_mul_conj_self, integral_mul_conj_self, hφnorm] at hU'
    exact_mod_cast hU'

  have hDsq : ∀ (e : ιE) (j : Fin (nE e)) (τ : ℝ),
      (∫ k, ‖((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
          deriv (fun s : ℂ => NE e j s (k : AdelicGL2 (𝓞 L) L)) ((τ : ℂ) * Complex.I)‖ ^ 2
          ∂(maximalCompactHaar L)) ≤ (d * G e τ ^ A) ^ 2 := by
    intro e j τ
    have he : 0 < nE e := Fin.pos j
    have h := hS hαm (μE e) (νE e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (hμν e)
      (τμ e) (τν e) (hτμ e) (hτν e) (mμ e) (mν e) (hmμ e) (hmν e) (φE e j) (hφE e j) (hφEK e j)
      (hφEf e j) (hφEjc e j) (hφEhol e j) (hφEKu e j) (hφEflat e j) (hφElev e j) (hφEty e j) (hφn e j)
      (OE e j) (EE e j) (NE e j) (hEE e j) τ
    refine h.trans (pow_le_pow_left₀ (mul_nonneg hCs0.le (pow_nonneg (le_trans zero_le_one
      (le_add_of_nonneg_right (Finset.sum_nonneg fun v _ => by positivity))) A)) ?_ 2)
    calc Cs * (1 + ∑ v : InfinitePlace L, (|τ + τμ e v| + |τ - τν e v| + (|mμ e v| : ℝ) + (|mν e v| : ℝ))) ^ A
        ≤ Cs * (Rm * G e τ) ^ A :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans zero_le_one
            (le_add_of_nonneg_right (Finset.sum_nonneg fun v _ => by positivity))) (hXle e he τ) A) hCs0.le
      _ = d * G e τ ^ A := by rw [hddef, mul_pow]; ring
  have hDsqσ : ∀ (e : ιE) (j : Fin (nE e)) (τ : ℝ),
      (∫ k, ‖((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
          deriv (fun s : ℂ => NE e j s (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ((τ : ℂ) * Complex.I)‖ ^ 2
          ∂(maximalCompactHaar L)) ≤ (d * G e τ ^ A) ^ 2 := by
    intro e j τ
    have e1 := hKsq (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        deriv (fun s : ℂ => NE e j s g) ((τ : ℂ) * Complex.I))
    beta_reduce at e1
    rw [e1]
    exact hDsq e j τ

  have hsegA : ∀ (e : ιE) {t t' τ : ℝ}, τ ∈ Set.uIcc t t' → (d * G e τ ^ A) ^ 2 ≤ (d * (G e t + G e t') ^ A) ^ 2 := by
    intro e t t' τ hτ
    have hle : G e τ ≤ G e t + G e t' := gauge_le_add_of_mem_uIcc (τμ e) (τν e) hτ
    have h1 : d * G e τ ^ A ≤ d * (G e t + G e t') ^ A :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hG0 e τ).le hle A) hd0
    exact pow_le_pow_left₀ (mul_nonneg hd0 (pow_nonneg (hG0 e τ).le A)) h1 2

  have hGcont : ∀ e, Continuous (G e) := by
    intro e
    refine continuous_const.add (continuous_finsetSum _ fun v _ => ?_)
    exact ((continuous_id.add continuous_const).abs).add ((continuous_id.sub continuous_const).abs)
  have hPdef : ∀ e i j, P e i j = ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 L) L) *
      conj (φE e j 0 (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(maximalCompactHaar L) :=
    fun _ _ _ => rfl
  have hUdef : ∀ e i j t, U e i j t = ∫ k, φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) *
      conj (((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        NE e j ((t : ℂ) * Complex.I) (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(maximalCompactHaar L) :=
    fun _ _ _ _ => rfl
  have hVdef : ∀ e i j t, V e i j t = ∫ k, (((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        NE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) *
      conj (φE e j ((t : ℂ) * Complex.I) (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(maximalCompactHaar L) :=
    fun _ _ _ _ => rfl
  have hQdef : ∀ e i j t, Q e i j t = ∫ k, (((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        NE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) *
      conj (((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        deriv (fun s : ℂ => NE e j s (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ((t : ℂ) * Complex.I))
        ∂(maximalCompactHaar L) :=
    fun _ _ _ _ => rfl
  have hsq_le : ∀ {x y : ℝ}, 0 ≤ y → x ≤ y ^ 2 → Real.sqrt x ≤ y := fun {x y} hy h => by
    rw [← Real.sqrt_sq hy]; exact Real.sqrt_le_sqrt h
  have hP_le : ∀ e i j, ‖P e i j‖ ≤ 1 := by
    intro e i j
    have h := norm_integral_mul_conj_le L (fun k => φE e i 0 (k : AdelicGL2 (𝓞 L) L))
      (fun k => φE e j 0 (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) (hφK e i 0) (hφKσ e j 0)
    beta_reduce at h
    have e1 := hKsq (φE e j 0)
    rw [e1, hφnorm, hφnorm, Real.sqrt_one, mul_one] at h
    rw [hPdef]; exact h
  have hU_le : ∀ e i j t, ‖U e i j t‖ ≤ 1 := by
    intro e i j t
    have h := norm_integral_mul_conj_le L (fun k => φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L))
      (fun k => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        NE e j ((t : ℂ) * Complex.I) (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L)))
      (hφK e i _) (hNKσ e j t)
    beta_reduce at h
    have e1 := hKsq (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g)
    beta_reduce at e1
    rw [e1, hφnorm, hNnorm, Real.sqrt_one, mul_one] at h
    rw [hUdef]; exact h
  have hV_le : ∀ e i j t, ‖V e i j t‖ ≤ 1 := by
    intro e i j t
    have h := norm_integral_mul_conj_le L
      (fun k => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        NE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L))
      (fun k => φE e j ((t : ℂ) * Complex.I) (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L)))
      (hNK e i t) (hφKσ e j _)
    beta_reduce at h
    have e1 := hKsq (φE e j ((t : ℂ) * Complex.I))
    rw [e1, hφnorm, hNnorm, Real.sqrt_one, mul_one] at h
    rw [hVdef]; exact h
  have hQ_le : ∀ e i j t, ‖Q e i j t‖ ≤ d * G e t ^ A := by
    intro e i j t
    have h := norm_integral_mul_conj_le L
      (fun k => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        NE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L))
      (fun k => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        deriv (fun s : ℂ => NE e j s (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ((t : ℂ) * Complex.I))
      (hNK e i t) (hDKσ e j t)
    beta_reduce at h
    rw [hNnorm, Real.sqrt_one, one_mul] at h
    have h2 := hsq_le (mul_nonneg hd0 (pow_nonneg (hG0 e t).le A)) (hDsqσ e j t)
    rw [hQdef]; exact h.trans h2
  have hUdiff : ∀ e i j t t', ‖U e i j t - U e i j t'‖ ≤ d * (G e t + G e t') ^ A * |t - t'| := by
    intro e i j t t'
    have hr : ∀ τ : ℝ, U e i j τ = ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 L) L) *
        conj (((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
          NE e j ((τ : ℂ) * Complex.I) (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(maximalCompactHaar L) := by
      intro τ; rw [hUdef]
      exact integral_congr_ae (Eventually.of_forall fun k => by simp only [hφEflat e i _ k])
    rw [hr t, hr t', integral_mul_conj_sub L _ _ _ (hφK e i 0) (hNKσ e j t) (hNKσ e j t')]
    have h := norm_integral_mul_conj_le L (fun k => φE e i 0 (k : AdelicGL2 (𝓞 L) L))
      (fun k => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
          NE e j ((t : ℂ) * Complex.I) (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L)) -
        ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
          NE e j ((t' : ℂ) * Complex.I) (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L)))
      (hφK e i 0) ((hNKσ e j t).sub (hNKσ e j t'))
    beta_reduce at h
    rw [hφnorm, Real.sqrt_one, one_mul] at h
    have hnn : 0 ≤ d * (G e t + G e t') ^ A * |t - t'| :=
      mul_nonneg (mul_nonneg hd0 (pow_nonneg (add_nonneg (hG0 e t).le (hG0 e t').le) A)) (abs_nonneg _)
    have hlip := lipschitz_on_K L (NE e j) (OE e j) (hopen e j) (hax e j) (hanN e j) (hcontN e j)
      (sigmaAdelicAct K L D σ.symm) hσc ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ t t'
      (d * (G e t + G e t') ^ A) (fun τ hτ => (hDsqσ e j τ).trans (hsegA e hτ))
    exact h.trans (hsq_le hnn hlip)
  have hVdiff : ∀ e i j t t', ‖V e i j t - V e i j t'‖ ≤ d * (G e t + G e t') ^ A * |t - t'| := by
    intro e i j t t'
    have hr : ∀ τ : ℝ, V e i j τ = ∫ k, (((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        NE e i ((τ : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) *
        conj (φE e j 0 (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(maximalCompactHaar L) := by
      intro τ; rw [hVdef]
      exact integral_congr_ae (Eventually.of_forall fun k => by simp only [hflatσ e j _ k])
    rw [hr t, hr t', integral_mul_conj_sub' L _ _ _ (hNK e i t) (hNK e i t') (hφKσ e j 0)]
    have h := norm_integral_mul_conj_le L
      (fun k => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
          NE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) -
        ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
          NE e i ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L))
      (fun k => φE e j 0 (sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L)))
      ((hNK e i t).sub (hNK e i t')) (hφKσ e j 0)
    beta_reduce at h
    have e1 := hKsq (φE e j 0)
    rw [e1, hφnorm, Real.sqrt_one, mul_one] at h
    have hnn : 0 ≤ d * (G e t + G e t') ^ A * |t - t'| :=
      mul_nonneg (mul_nonneg hd0 (pow_nonneg (add_nonneg (hG0 e t).le (hG0 e t').le) A)) (abs_nonneg _)
    have hlip := lipschitz_on_K L (NE e i) (OE e i) (hopen e i) (hax e i) (hanN e i) (hcontN e i)
      id continuous_id ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ t t'
      (d * (G e t + G e t') ^ A) (fun τ hτ => (hDsq e i τ).trans (hsegA e hτ))
    exact h.trans (hsq_le hnn hlip)

  have hcontNσ : ∀ e j, ContinuousOn
      (fun p : ℂ × AdelicGL2 (𝓞 L) L => NE e j p.1 (sigmaAdelicAct K L D σ.symm p.2)) ((OE e j) ×ˢ Set.univ) := by
    intro e j
    have h2 : Continuous fun p : ℂ × AdelicGL2 (𝓞 L) L => ((p.1, sigmaAdelicAct K L D σ.symm p.2) : ℂ × AdelicGL2 (𝓞 L) L) :=
      continuous_fst.prodMk (hσc.comp continuous_snd)
    exact (hcontN e j).comp h2.continuousOn (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
  have hφjc : ∀ e j, Continuous fun p : ℝ × adelicMaximalCompact L =>
      φE e j ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 L) L) := fun e j =>
    (hφEjc e j).comp (continuous_axis_coe L id continuous_id)
  have hφjcσ : ∀ e j, Continuous fun p : ℝ × adelicMaximalCompact L =>
      φE e j ((p.1 : ℂ) * Complex.I) (sigmaAdelicAct K L D σ.symm (p.2 : AdelicGL2 (𝓞 L) L)) := fun e j =>
    (hφEjc e j).comp (continuous_axis_coe L _ hσc)
  have hNjc : ∀ e j, Continuous fun p : ℝ × adelicMaximalCompact L =>
      ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        NE e j ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 L) L) := fun e j =>
    continuous_const.mul (continuous_eval_axis L (hax e j) (NE e j) (hcontN e j) id continuous_id)
  have hNjcσ : ∀ e j, Continuous fun p : ℝ × adelicMaximalCompact L =>
      ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        NE e j ((p.1 : ℂ) * Complex.I) (sigmaAdelicAct K L D σ.symm (p.2 : AdelicGL2 (𝓞 L) L)) := fun e j =>
    continuous_const.mul (continuous_eval_axis L (hax e j) (NE e j) (hcontN e j) _ hσc)
  have hDjcσ : ∀ e j, Continuous fun p : ℝ × adelicMaximalCompact L =>
      ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ *
        deriv (fun s : ℂ => NE e j s (sigmaAdelicAct K L D σ.symm (p.2 : AdelicGL2 (𝓞 L) L))) ((p.1 : ℂ) * Complex.I) :=
    fun e j => continuous_const.mul (continuous_deriv_eval_axis L (hopen e j) (hax e j) (NE e j) (hcontN e j)
      (hanN e j) _ hσc)
  have hCa : ∀ e i j, Continuous (a e i j) := fun e i j => (hdiffa e i j).continuous
  have hCQ : ∀ e i j, Continuous (Q e i j) := fun e i j =>
    continuous_integral_K L ((hNjc e i).mul (Complex.continuous_conj.comp (hDjcσ e j)))
  have hCU : ∀ e i j, Continuous (U e i j) := fun e i j =>
    continuous_integral_K L ((hφjc e i).mul (Complex.continuous_conj.comp (hNjcσ e j)))
  have hCV : ∀ e i j, Continuous (V e i j) := fun e i j =>
    continuous_integral_K L ((hNjc e i).mul (Complex.continuous_conj.comp (hφjcσ e j)))

  have hα1 : ∀ e i j t, ‖a e i j t‖ ≤ c * (G e t ^ M)⁻¹ := by
    intro e i j t
    refine le_trans ?_ (hcbound e t)
    calc ‖a e i j t‖ ≤ ‖a e i j t‖ + ‖deriv (a e i j) t‖ := le_add_of_nonneg_right (norm_nonneg _)
      _ ≤ ∑ j', (‖a e i j' t‖ + ‖deriv (a e i j') t‖) :=
          Finset.single_le_sum (f := fun j' => ‖a e i j' t‖ + ‖deriv (a e i j') t‖)
            (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖a e i' j' t‖ + ‖deriv (a e i' j') t‖) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖a e i' j' t‖ + ‖deriv (a e i' j') t‖))
            (fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)
  have hαsum : ∀ e t, (∑ i, ∑ j, ‖a e i j t‖) ≤ c * (G e t ^ M)⁻¹ := fun e t =>
    (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      le_add_of_nonneg_right (norm_nonneg (deriv (a e i j) t))).trans (hcbound e t)
  have hα'sum : ∀ e t, (∑ i, ∑ j, ‖deriv (a e i j) t‖) ≤ c * (G e t ^ M)⁻¹ := fun e t =>
    (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      le_add_of_nonneg_left (norm_nonneg (a e i j t))).trans (hcbound e t)
  have hIa : ∀ e i j, Integrable (a e i j) := fun e i j =>
    Integrable.mono' ((hintM e).const_mul c) (hCa e i j).aestronglyMeasurable (Eventually.of_forall (hα1 e i j))
  have hIaQ : ∀ e i j, Integrable (fun t => a e i j t * Q e i j t) := by
    intro e i j
    refine Integrable.mono' ((hintM₀ e).const_mul (c * d)) ((hCa e i j).mul (hCQ e i j)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    calc ‖a e i j t‖ * ‖Q e i j t‖ ≤ (c * (G e t ^ M)⁻¹) * (d * G e t ^ A) :=
          mul_le_mul (hα1 e i j t) (hQ_le e i j t) (norm_nonneg _)
            (mul_nonneg hc0 (inv_nonneg.mpr (pow_nonneg (hG0 e t).le _)))
      _ = c * d * (G e t ^ B₀)⁻¹ := by rw [← hGA e t]; ring
  have hIaU : ∀ e i j, Integrable (fun t => a e i j t * U e i j t) := by
    intro e i j
    refine Integrable.mono' (hIa e i j).norm ((hCa e i j).mul (hCU e i j)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hU_le e i j t) (norm_nonneg _)).trans (mul_one _).le
  have hIaV : ∀ e i j, Integrable (fun t => a e i j t * V e i j t) := by
    intro e i j
    refine Integrable.mono' (hIa e i j).norm ((hCa e i j).mul (hCV e i j)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hV_le e i j t) (norm_nonneg _)).trans (mul_one _).le

  have hinv0 : ∀ e t (m : ℕ), 0 ≤ (G e t ^ m)⁻¹ := fun e t m => inv_nonneg.mpr (pow_nonneg (hG0 e t).le _)

  set C₁ : ℝ := c * (4 + d) with hC₁
  set C₂ : ℝ := 2 * c * R ^ B₀ with hC₂
  set C₃ : ℝ := R ^ B₀ * (2 * c * R ^ M + 2 * c * d * (R + 1) ^ A) + 4 * c * R ^ B₀ with hC₃
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  set Cbig : ℝ := C₁ + C₂ + C₃ with hCbig
  have hle₁ : C₁ ≤ Cbig := by rw [hCbig]; linarith
  have hle₂ : C₂ ≤ Cbig := by rw [hCbig]; linarith
  have hle₃ : C₃ ≤ Cbig := by rw [hCbig]; linarith

  have hempty : ∀ e, ¬ 0 < nE e → IsEmpty (Fin (nE e)) := fun e he => by
    rw [Nat.eq_zero_of_not_pos he]; infer_instance

  have hL1 : ∀ e, 0 < nE e → (∑ i : Fin (nE e), ∑ j : Fin (nE e),
      ∫ t : ℝ, (‖a e i j t‖ * (1 + ‖P e i j‖) + ‖a e i j t * Q e i j t‖ +
        ‖a e i j t * U e i j t‖ + ‖a e i j t * V e i j t‖)) ≤ C₁ * Bi e := by
    intro e hne

    have hpt : ∀ i j t, (‖a e i j t‖ * (1 + ‖P e i j‖) + ‖a e i j t * Q e i j t‖ +
        ‖a e i j t * U e i j t‖ + ‖a e i j t * V e i j t‖) ≤ ‖a e i j t‖ * (4 + d * G e t ^ A) := by
      intro i j t
      rw [norm_mul, norm_mul, norm_mul]
      have ha0 := norm_nonneg (a e i j t)
      have h1 : ‖a e i j t‖ * (1 + ‖P e i j‖) ≤ ‖a e i j t‖ * 2 :=
        mul_le_mul_of_nonneg_left (by linarith [hP_le e i j]) ha0
      have h2 : ‖a e i j t‖ * ‖Q e i j t‖ ≤ ‖a e i j t‖ * (d * G e t ^ A) :=
        mul_le_mul_of_nonneg_left (hQ_le e i j t) ha0
      have h3 : ‖a e i j t‖ * ‖U e i j t‖ ≤ ‖a e i j t‖ * 1 := mul_le_mul_of_nonneg_left (hU_le e i j t) ha0
      have h4 : ‖a e i j t‖ * ‖V e i j t‖ ≤ ‖a e i j t‖ * 1 := mul_le_mul_of_nonneg_left (hV_le e i j t) ha0
      nlinarith

    have hint_f : ∀ i j, Integrable (fun t : ℝ => ‖a e i j t‖ * (1 + ‖P e i j‖) + ‖a e i j t * Q e i j t‖ +
        ‖a e i j t * U e i j t‖ + ‖a e i j t * V e i j t‖) := fun i j =>
      ((((hIa e i j).norm.mul_const _).add (hIaQ e i j).norm).add (hIaU e i j).norm).add (hIaV e i j).norm
    have hbound_g : ∀ i j t, ‖a e i j t‖ * (4 + d * G e t ^ A) ≤ c * (4 + d) * (G e t ^ B₀)⁻¹ := by
      intro i j t
      calc ‖a e i j t‖ * (4 + d * G e t ^ A) ≤ c * (G e t ^ M)⁻¹ * (4 + d * G e t ^ A) :=
            mul_le_mul_of_nonneg_right (hα1 e i j t) (by have := pow_nonneg (hG0 e t).le A; positivity)
        _ = 4 * c * (G e t ^ M)⁻¹ + c * d * (G e t ^ A * (G e t ^ M)⁻¹) := by ring
        _ ≤ 4 * c * (G e t ^ B₀)⁻¹ + c * d * (G e t ^ B₀)⁻¹ := by
            rw [hGA e t]
            have := mul_le_mul_of_nonneg_left (hpowmono e t) (by positivity : (0 : ℝ) ≤ 4 * c)
            linarith
        _ = c * (4 + d) * (G e t ^ B₀)⁻¹ := by ring
    have hint_g : ∀ i j, Integrable (fun t : ℝ => ‖a e i j t‖ * (4 + d * G e t ^ A)) := fun i j =>
      Integrable.mono' ((hintM₀ e).const_mul (c * (4 + d)))
        ((hCa e i j).norm.mul (continuous_const.add (continuous_const.mul ((hGcont e).pow A)))).aestronglyMeasurable
        (Eventually.of_forall fun t => by
          rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (by have := pow_nonneg (hG0 e t).le A; positivity))]
          exact hbound_g i j t)
    have hsum_pt : ∀ t, (∑ i, ∑ j, ‖a e i j t‖ * (4 + d * G e t ^ A)) ≤ c * (4 + d) * (G e t ^ B₀)⁻¹ := by
      intro t
      rw [show (∑ i, ∑ j, ‖a e i j t‖ * (4 + d * G e t ^ A)) = (∑ i, ∑ j, ‖a e i j t‖) * (4 + d * G e t ^ A) by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.sum_mul]]
      calc (∑ i, ∑ j, ‖a e i j t‖) * (4 + d * G e t ^ A) ≤ c * (G e t ^ M)⁻¹ * (4 + d * G e t ^ A) :=
            mul_le_mul_of_nonneg_right (hαsum e t) (by have := pow_nonneg (hG0 e t).le A; positivity)
        _ = 4 * c * (G e t ^ M)⁻¹ + c * d * (G e t ^ A * (G e t ^ M)⁻¹) := by ring
        _ ≤ 4 * c * (G e t ^ B₀)⁻¹ + c * d * (G e t ^ B₀)⁻¹ := by
            rw [hGA e t]
            have := mul_le_mul_of_nonneg_left (hpowmono e t) (by positivity : (0 : ℝ) ≤ 4 * c)
            linarith
        _ = c * (4 + d) * (G e t ^ B₀)⁻¹ := by ring
    calc (∑ i, ∑ j, ∫ t : ℝ, (‖a e i j t‖ * (1 + ‖P e i j‖) + ‖a e i j t * Q e i j t‖ +
          ‖a e i j t * U e i j t‖ + ‖a e i j t * V e i j t‖))
        ≤ ∑ i, ∑ j, ∫ t : ℝ, ‖a e i j t‖ * (4 + d * G e t ^ A) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            integral_mono (hint_f i j) (hint_g i j) (hpt i j)
      _ = ∑ i, ∫ t : ℝ, ∑ j, ‖a e i j t‖ * (4 + d * G e t ^ A) :=
          Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun j _ => hint_g i j).symm
      _ = ∫ t : ℝ, ∑ i, ∑ j, ‖a e i j t‖ * (4 + d * G e t ^ A) :=
          (integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint_g i j).symm
      _ ≤ ∫ t : ℝ, c * (4 + d) * (G e t ^ B₀)⁻¹ :=
          integral_mono (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint_g i j)
            ((hintM₀ e).const_mul _) hsum_pt
      _ = C₁ * Bi e := integral_const_mul _ _

  have hSUP : ∀ e t, 0 < nE e →
      (∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖a e i j t‖ * (‖U e i j t‖ + ‖V e i j t‖)) ≤ C₂ * Bi e := by
    intro e t hne
    calc (∑ i, ∑ j, ‖a e i j t‖ * (‖U e i j t‖ + ‖V e i j t‖))
        ≤ ∑ i, ∑ j, ‖a e i j t‖ * 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (by linarith [hU_le e i j t, hV_le e i j t]) (norm_nonneg _)
      _ = (∑ i, ∑ j, ‖a e i j t‖) * 2 := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.sum_mul]
      _ ≤ c * (G e t ^ M)⁻¹ * 2 := mul_le_mul_of_nonneg_right (hαsum e t) zero_le_two
      _ ≤ c * (R ^ B₀ * Bi e) * 2 := by
          have := mul_le_mul_of_nonneg_left (hlocM e t) hc0
          linarith
      _ = C₂ * Bi e := by rw [hC₂]; ring

  have hLIP : ∀ (W : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ),
      (∀ e i j t, ‖W e i j t‖ ≤ 2) →
      (∀ e i j t t', ‖W e i j t - W e i j t'‖ ≤ 2 * d * (G e t + G e t') ^ A * |t - t'|) →
      ∀ e t t', 0 < nE e →
        (∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖a e i j t * W e i j t - a e i j t' * W e i j t'‖) ≤
          C₃ * Bi e * |t - t'| := by
    intro W hW hWd e t t' hne
    have hBe := hBi0 e
    rcases le_or_gt |t - t'| 1 with hsmall | hlarge
    ·
      have hGt' : G e t' ≤ R * G e t := hGcmp e (by rwa [abs_sub_comm] at hsmall)

      have hderiv_bd : ∀ s, |t - s| ≤ 1 → (∑ i, ∑ j, ‖deriv (a e i j) s‖) ≤ c * R ^ M * (G e t ^ M)⁻¹ := by
        intro s hs
        calc (∑ i, ∑ j, ‖deriv (a e i j) s‖) ≤ c * (G e s ^ M)⁻¹ := hα'sum e s
          _ ≤ c * (R ^ M * (G e t ^ M)⁻¹) := mul_le_mul_of_nonneg_left (hcmp e M hs) hc0
          _ = c * R ^ M * (G e t ^ M)⁻¹ := by ring
      have hda : (∑ i, ∑ j, ‖a e i j t - a e i j t'‖) ≤ c * R ^ M * (G e t ^ M)⁻¹ * |t - t'| := by
        rcases le_total t' t with h | h
        · have := sum_norm_sub_le_of_deriv (a e) (hdiffa e) (hCderiv e) (c * R ^ M * (G e t ^ M)⁻¹) h
            (fun s hs => hderiv_bd s (by
              rw [abs_le]; constructor <;> [linarith [hs.1, hs.2, abs_le.mp hsmall];
                linarith [hs.1, hs.2, (abs_le.mp hsmall).1, (abs_le.mp hsmall).2]]))
          rwa [abs_of_nonneg (by linarith : 0 ≤ t - t')]
        · have := sum_norm_sub_le_of_deriv (a e) (hdiffa e) (hCderiv e) (c * R ^ M * (G e t ^ M)⁻¹) h
            (fun s hs => hderiv_bd s (by
              rw [abs_le]; constructor <;>
                linarith [hs.1, hs.2, (abs_le.mp hsmall).1, (abs_le.mp hsmall).2]))
          rw [abs_of_nonpos (by linarith : t - t' ≤ 0), neg_sub]
          calc (∑ i, ∑ j, ‖a e i j t - a e i j t'‖) = ∑ i, ∑ j, ‖a e i j t' - a e i j t‖ := by
                simp_rw [norm_sub_rev (a e _ _ t)]
            _ ≤ c * R ^ M * (G e t ^ M)⁻¹ * (t' - t) := this

      have hsplit : ∀ i j, ‖a e i j t * W e i j t - a e i j t' * W e i j t'‖ ≤
          ‖a e i j t‖ * (2 * d * (G e t + G e t') ^ A * |t - t'|) + ‖a e i j t - a e i j t'‖ * 2 := by
        intro i j
        have e1 : a e i j t * W e i j t - a e i j t' * W e i j t' =
            a e i j t * (W e i j t - W e i j t') + (a e i j t - a e i j t') * W e i j t' := by ring
        rw [e1]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hWd e i j t t') (norm_nonneg _)
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hW e i j t') (norm_nonneg _)
      have hpowA : (G e t + G e t') ^ A ≤ (R + 1) ^ A * G e t ^ A := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (add_nonneg (hG0 e t).le (hG0 e t').le) (by linarith) A
      have habs0 : 0 ≤ |t - t'| := abs_nonneg _
      calc (∑ i, ∑ j, ‖a e i j t * W e i j t - a e i j t' * W e i j t'‖)
          ≤ ∑ i, ∑ j, (‖a e i j t‖ * (2 * d * (G e t + G e t') ^ A * |t - t'|) + ‖a e i j t - a e i j t'‖ * 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsplit i j
        _ = (∑ i, ∑ j, ‖a e i j t‖) * (2 * d * (G e t + G e t') ^ A * |t - t'|) +
              (∑ i, ∑ j, ‖a e i j t - a e i j t'‖) * 2 := by
            rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
        _ ≤ (c * (G e t ^ M)⁻¹) * (2 * d * ((R + 1) ^ A * G e t ^ A) * |t - t'|) +
              (c * R ^ M * (G e t ^ M)⁻¹ * |t - t'|) * 2 := by
            refine add_le_add (mul_le_mul (hαsum e t) ?_ (by positivity) (mul_nonneg hc0 (hinv0 e t M)))
              (mul_le_mul_of_nonneg_right hda zero_le_two)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowA (by positivity)) habs0
        _ = (2 * c * d * (R + 1) ^ A * (G e t ^ A * (G e t ^ M)⁻¹) + 2 * c * R ^ M * (G e t ^ M)⁻¹) * |t - t'| := by
            ring
        _ ≤ (2 * c * d * (R + 1) ^ A * (R ^ B₀ * Bi e) + 2 * c * R ^ M * (R ^ B₀ * Bi e)) * |t - t'| := by
            rw [hGA e t]
            refine mul_le_mul_of_nonneg_right (add_le_add ?_ ?_) habs0
            · exact mul_le_mul_of_nonneg_left (hloc e t) (by positivity)
            · exact mul_le_mul_of_nonneg_left (hlocM e t) (by positivity)
        _ ≤ C₃ * Bi e * |t - t'| := by
            rw [hC₃]
            have h4 : 0 ≤ 4 * c * R ^ B₀ * Bi e * |t - t'| := by positivity
            nlinarith
    ·
      have hterm : ∀ i j, ‖a e i j t * W e i j t - a e i j t' * W e i j t'‖ ≤ ‖a e i j t‖ * 2 + ‖a e i j t'‖ * 2 := by
        intro i j
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hW e i j t) (norm_nonneg _)
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hW e i j t') (norm_nonneg _)
      calc (∑ i, ∑ j, ‖a e i j t * W e i j t - a e i j t' * W e i j t'‖)
          ≤ ∑ i, ∑ j, (‖a e i j t‖ * 2 + ‖a e i j t'‖ * 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = (∑ i, ∑ j, ‖a e i j t‖) * 2 + (∑ i, ∑ j, ‖a e i j t'‖) * 2 := by
            rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
        _ ≤ (c * (G e t ^ M)⁻¹) * 2 + (c * (G e t' ^ M)⁻¹) * 2 :=
            add_le_add (mul_le_mul_of_nonneg_right (hαsum e t) zero_le_two)
              (mul_le_mul_of_nonneg_right (hαsum e t') zero_le_two)
        _ ≤ (c * (R ^ B₀ * Bi e)) * 2 + (c * (R ^ B₀ * Bi e)) * 2 :=
            add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hlocM e t) hc0) zero_le_two)
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hlocM e t') hc0) zero_le_two)
        _ = 4 * c * R ^ B₀ * Bi e * 1 := by ring
        _ ≤ 4 * c * R ^ B₀ * Bi e * |t - t'| :=
            mul_le_mul_of_nonneg_left hlarge.le (by positivity)
        _ ≤ C₃ * Bi e * |t - t'| := by
            rw [hC₃]
            have h4 : 0 ≤ R ^ B₀ * (2 * c * R ^ M + 2 * c * d * (R + 1) ^ A) * Bi e * |t - t'| := by positivity
            nlinarith

  refine ⟨hCa, hCQ, hCU, hCV, hIa, hIaQ, hIaU, hIaV,
    ⟨fun e => Cbig * (if 0 < nE e then Bi e else 0), hsumB.mul_left Cbig, ?_, ?_, ?_⟩⟩
  · intro e
    by_cases hne : 0 < nE e
    · beta_reduce; rw [if_pos hne]
      exact (hL1 e hne).trans (mul_le_mul_of_nonneg_right hle₁ (hBi0 e))
    · haveI := hempty e hne; simp [hne]
  · intro e t
    by_cases hne : 0 < nE e
    · beta_reduce; rw [if_pos hne]
      exact (hSUP e t hne).trans (mul_le_mul_of_nonneg_right hle₂ (hBi0 e))
    · haveI := hempty e hne; simp [hne]
  · intro e t t'
    by_cases hne : 0 < nE e
    · beta_reduce; rw [if_pos hne]
      have hW1 : ∀ e i j t, ‖U e i j t + V e i j t‖ ≤ 2 := fun e i j t =>
        (norm_add_le _ _).trans (by linarith [hU_le e i j t, hV_le e i j t])
      have hW2 : ∀ e i j t, ‖U e i j t - V e i j t‖ ≤ 2 := fun e i j t =>
        (norm_sub_le _ _).trans (by linarith [hU_le e i j t, hV_le e i j t])
      have hW1d : ∀ e i j t t', ‖(U e i j t + V e i j t) - (U e i j t' + V e i j t')‖ ≤
          2 * d * (G e t + G e t') ^ A * |t - t'| := by
        intro e i j t t'
        rw [show (U e i j t + V e i j t) - (U e i j t' + V e i j t') =
          (U e i j t - U e i j t') + (V e i j t - V e i j t') by ring]
        refine (norm_add_le _ _).trans ?_
        have := hUdiff e i j t t'; have := hVdiff e i j t t'; linarith
      have hW2d : ∀ e i j t t', ‖(U e i j t - V e i j t) - (U e i j t' - V e i j t')‖ ≤
          2 * d * (G e t + G e t') ^ A * |t - t'| := by
        intro e i j t t'
        rw [show (U e i j t - V e i j t) - (U e i j t' - V e i j t') =
          (U e i j t - U e i j t') - (V e i j t - V e i j t') by ring]
        refine (norm_sub_le _ _).trans ?_
        have := hUdiff e i j t t'; have := hVdiff e i j t t'; linarith
      have k1 := hLIP (fun e i j t => U e i j t + V e i j t) hW1 hW1d e t t' hne
      have k2 := hLIP (fun e i j t => U e i j t - V e i j t) hW2 hW2d e t t' hne
      beta_reduce at k1 k2
      have hfin : C₃ * Bi e * |t - t'| ≤ Cbig * Bi e * |t - t'| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle₃ (hBi0 e)) (abs_nonneg _)
      exact ⟨k1.trans hfin, k2.trans hfin⟩
    · haveI := hempty e hne; simp [hne]

end S_AutomorphicForm_exists_summable_dominant_rightConv_axis_family_sigma_maassSelberg_pairings_of_isSemiLocalFactorization_lipschitz
end P2MW
export P2MW.S_AutomorphicForm_exists_summable_dominant_rightConv_axis_family_sigma_maassSelberg_pairings_of_isSemiLocalFactorization_lipschitz (solution)
