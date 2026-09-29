-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_mul_pow_of_eq_or_exists_normOneIdeles_of_isArchCompAt_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/cb31ad81-2d3a-5d0b-8bfb-b8f2055e14c5

import Theorems.Thm_AutomorphicForm_exists_forall_integral_maximalCompact_norm_sq_deriv_axis_continuation_weylIntertwiningIntegral_le_and_norm_sq_sub_le_of_flat_of_ne_bot
import Theorems.Thm_AutomorphicForm_continuous_and_hasDerivAt_axis_continuation_weylIntertwiningIntegral_pairings_of_flat
import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_of_flat_of_eLpNorm_deriv_le
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_NumberField_NormPowChar
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_mul_pow_of_eq_or_exists_normOneIdeles_of_isArchCompAt_of_ne_bot
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

noncomputable section

namespace R4MsL2Fam

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm NumberField.TateGlobal
open Set Filter Metric
open scoped ComplexConjugate Topology ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section General

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

theorem eLpNorm_two_eq_ofReal_sqrt {g : X → ℂ} (hg : MemLp g 2 m) :
    eLpNorm g 2 m = ENNReal.ofReal (Real.sqrt (∫ k, ‖g k‖ ^ 2 ∂m)) := by
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  congr 1
  rw [ENNReal.toReal_ofNat, Real.sqrt_eq_rpow, one_div]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  simp

theorem eLpNorm_le_of_integral_sq_le {g : X → ℂ} (hg : MemLp g 2 m) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫ k, ‖g k‖ ^ 2 ∂m ≤ B ^ 2) : eLpNorm g 2 m ≤ ENNReal.ofReal B := by
  rw [eLpNorm_two_eq_ofReal_sqrt hg]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.sqrt (∫ k, ‖g k‖ ^ 2 ∂m) ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt h
    _ = B := Real.sqrt_sq hB

theorem integral_mul_conj_self_eq (f : X → ℂ) :
    ∫ k, f k * conj (f k) ∂m = ((∫ k, ‖f k‖ ^ 2 ∂m : ℝ) : ℂ) := by
  have h : ∀ k, f k * conj (f k) = ((‖f k‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [h]
  exact integral_ofReal

theorem integral_norm_sq_eq_of {f : X → ℂ} {P : ℝ}
    (hf : ∫ k, f k * conj (f k) ∂m = (P : ℂ)) : ∫ k, ‖f k‖ ^ 2 ∂m = P := by
  rw [integral_mul_conj_self_eq] at hf
  exact_mod_cast hf

theorem sqrt_integral_le {g : X → ℂ} {B : ℝ} (hB : 0 ≤ B) (h : ∫ k, ‖g k‖ ^ 2 ∂m ≤ B ^ 2) :
    Real.sqrt (∫ k, ‖g k‖ ^ 2 ∂m) ≤ B :=
  (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq hB)

end General

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

variable (F : Type) [Field F] [NumberField F]

theorem memLp_two_of_continuous {f : adelicMaximalCompact F → ℂ} (hf : Continuous f) :
    MemLp f 2 (maximalCompactHaar F) := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := adelicMaximalCompact F)).exists_bound_of_continuousOn
    hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => hC x (mem_univ _))

theorem axis_mem {O : Set ℂ} (hO : {s : ℂ | s.re = 0} ⊆ O) (t : ℝ) : (t : ℂ) * Complex.I ∈ O :=
  hO (by simp [Complex.mul_re])

theorem continuous_deriv_eval {O : Set ℂ} (hO : IsOpen O) (N : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hNa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => N s g) O)
    (hNc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => N p.1 p.2) (O ×ˢ univ))
    {s₀ : ℂ} (hs₀ : s₀ ∈ O) (c : ℂ) :
    Continuous fun k : adelicMaximalCompact F =>
      c * deriv (fun s : ℂ => N s (k : AdelicGL2 (𝓞 F) F)) s₀ := by
  have h := continuousOn_deriv_param N O hO hNc hNa
  have h2 : Continuous fun k : adelicMaximalCompact F =>
      deriv (fun s : ℂ => N s (k : AdelicGL2 (𝓞 F) F)) s₀ :=
    h.comp_continuous (continuous_const.prodMk continuous_subtype_val) fun k => ⟨hs₀, mem_univ _⟩
  exact continuous_const.mul h2

theorem eLpNorm_deriv_le {O : Set ℂ} (hO : IsOpen O) (N : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hNa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => N s g) O)
    (hNc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => N p.1 p.2) (O ×ˢ univ))
    {s₀ : ℂ} (hs₀ : s₀ ∈ O) (c : ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫ k, ‖c * deriv (fun s : ℂ => N s (k : AdelicGL2 (𝓞 F) F)) s₀‖ ^ 2 ∂(maximalCompactHaar F) ≤ B ^ 2) :
    eLpNorm (fun k : adelicMaximalCompact F => c * deriv (fun s : ℂ => N s (k : AdelicGL2 (𝓞 F) F)) s₀)
      2 (maximalCompactHaar F) ≤ ENNReal.ofReal B :=
  eLpNorm_le_of_integral_sq_le (memLp_two_of_continuous F (continuous_deriv_eval F hO N hNa hNc hs₀ c)) hB h

theorem gauge_le_gauge_add (a : InfinitePlace F → ℂ) (σ t : ℝ) :
    (1 + ∑ w : InfinitePlace F, ‖2 * (σ : ℂ) * Complex.I + a w‖) ≤
      (1 + ∑ w : InfinitePlace F, ‖2 * (t : ℂ) * Complex.I + a w‖) +
        2 * (Fintype.card (InfinitePlace F)) * |σ - t| := by
  have h : ∀ w : InfinitePlace F,
      ‖2 * (σ : ℂ) * Complex.I + a w‖ ≤ ‖2 * (t : ℂ) * Complex.I + a w‖ + 2 * |σ - t| := by
    intro w
    have h1 : 2 * (σ : ℂ) * Complex.I + a w =
        (2 * ((σ - t : ℝ) : ℂ) * Complex.I) + (2 * (t : ℂ) * Complex.I + a w) := by
      push_cast; ring
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖(2 * ((σ - t : ℝ) : ℂ) * Complex.I)‖ = 2 * |σ - t| := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_two,
        Real.norm_eq_abs]
    linarith [h2]
  calc (1 + ∑ w : InfinitePlace F, ‖2 * (σ : ℂ) * Complex.I + a w‖)
      ≤ 1 + ∑ w : InfinitePlace F, (‖2 * (t : ℂ) * Complex.I + a w‖ + 2 * |σ - t|) := by
        gcongr with w _; exact h w
    _ = (1 + ∑ w : InfinitePlace F, ‖2 * (t : ℂ) * Complex.I + a w‖) +
        2 * (Fintype.card (InfinitePlace F)) * |σ - t| := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem one_le_gauge (a : InfinitePlace F → ℂ) (t : ℝ) :
    (1 : ℝ) ≤ 1 + ∑ w : InfinitePlace F, ‖2 * (t : ℂ) * Complex.I + a w‖ :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem gauge_diag_le (a : InfinitePlace F → ℂ) {σ : ℝ} (hσ : |σ| ≤ 1) :
    (1 + ∑ w : InfinitePlace F, ‖2 * (σ : ℂ) * Complex.I + (a w - a w)‖) ≤
      1 + 2 * (Fintype.card (InfinitePlace F)) := by
  have h : ∀ w : InfinitePlace F, ‖2 * (σ : ℂ) * Complex.I + (a w - a w)‖ ≤ 2 := fun w => by
    rw [sub_self, add_zero, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_two, Real.norm_eq_abs]
    linarith
  calc (1 + ∑ w : InfinitePlace F, ‖2 * (σ : ℂ) * Complex.I + (a w - a w)‖)
      ≤ 1 + ∑ _w : InfinitePlace F, (2 : ℝ) := by gcongr with w _; exact h w
    _ = 1 + 2 * (Fintype.card (InfinitePlace F)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem isUnitaryChar_normPowChar (τ : ℝ) : IsUnitaryChar (𝓞 F) F (normPowChar F τ) :=
  fun x => norm_coe_normPowChar_apply τ x

theorem isUnitaryChar_mul {χ ψ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχ : IsUnitaryChar (𝓞 F) F χ)
    (hψ : IsUnitaryChar (𝓞 F) F ψ) : IsUnitaryChar (𝓞 F) F (χ * ψ) := fun x => by
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hχ x, hψ x, mul_one]

theorem isIdeleClassChar_normPowChar (τ : ℝ) : IsIdeleClassChar (𝓞 F) F (normPowChar F τ) := by
  intro u
  apply normPowChar_eq_one_of_ideleNorm_eq_one
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
  unfold ideleNorm
  rw [show (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) u : (AdeleRing (𝓞 F) F)ˣ) =
      Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom u from rfl, h]
  rfl

theorem isIdeleClassChar_mul {χ ψ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχ : IsIdeleClassChar (𝓞 F) F χ)
    (hψ : IsIdeleClassChar (𝓞 F) F ψ) : IsIdeleClassChar (𝓞 F) F (χ * ψ) := fun u => by
  rw [MonoidHom.mul_apply, hχ u, hψ u, mul_one]

theorem continuous_normPowChar (τ : ℝ) :
    Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((normPowChar F τ z : ℂˣ) : ℂ) := by
  have hc := NumberField.TateGlobal.continuous_ideleNorm F
  have h1 : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ideleNorm F z : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hc
  have : (fun z : (AdeleRing (𝓞 F) F)ˣ => ((normPowChar F τ z : ℂˣ) : ℂ)) =
      fun z => ((ideleNorm F z : ℝ) : ℂ) ^ (Complex.I * τ) := by
    funext z; exact coe_normPowChar_apply τ z
  rw [this]
  refine h1.cpow continuous_const fun z => ?_
  exact Or.inl (by simpa using ideleNorm_pos z)

theorem continuous_mul_normPowChar {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hχ : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((χ z : ℂˣ) : ℂ)) (τ : ℝ) :
    Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => (((χ * normPowChar F τ) z : ℂˣ) : ℂ) := by
  have : (fun z : (AdeleRing (𝓞 F) F)ˣ => (((χ * normPowChar F τ) z : ℂˣ) : ℂ)) =
      fun z => ((χ z : ℂˣ) : ℂ) * ((normPowChar F τ z : ℂˣ) : ℂ) := by
    funext z; rw [MonoidHom.mul_apply, Units.val_mul]
  rw [this]
  exact hχ.mul (continuous_normPowChar F τ)

theorem normPowChar_apply_of_mem_normOneIdeles (τ : ℝ) {z : (AdeleRing (𝓞 F) F)ˣ}
    (hz : z ∈ normOneIdeles F) : normPowChar F τ z = 1 :=
  normPowChar_eq_one_of_ideleNorm_eq_one τ ((mem_normOneIdeles_iff z).1 hz)

theorem etaFst_mul_normPowChar (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (hαn : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x) (τ : ℝ) (s : ℂ) :
    etaFst (μ * normPowChar F τ) α hα s = etaFst μ α hα (s + (τ : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [etaFst_apply, etaFst_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    cpowChar_apply_val, cpowChar_apply_val, coe_normPowChar_apply, hαn]
  have hx : ((ideleNorm F x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ideleNorm_pos x).ne'
  rw [mul_assoc, ← Complex.cpow_add _ _ hx]
  congr 2; ring

theorem etaSnd_mul_normPowChar (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (hαn : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x) (τ : ℝ) (s : ℂ) :
    etaSnd (ν * normPowChar F (-τ)) α hα s = etaSnd ν α hα (s + (τ : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [etaSnd_apply, etaSnd_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    cpowChar_apply_val, cpowChar_apply_val, coe_normPowChar_apply, hαn]
  have hx : ((ideleNorm F x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ideleNorm_pos x).ne'
  rw [mul_assoc, ← Complex.cpow_add _ _ hx]
  congr 2; push_cast; ring

section Shift

variable {F}

theorem shift_isInducedSection (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαn : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x) {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s)) (τ : ℝ) (s : ℂ) :
    IsInducedSection (𝓞 F) F (etaFst (μ * normPowChar F τ) α hα s) (etaSnd (ν * normPowChar F (-τ)) α hα s)
      (φ (s + (τ : ℂ) * Complex.I)) := by
  rw [etaFst_mul_normPowChar F μ α hα hαn, etaSnd_mul_normPowChar F ν α hα hαn]
  exact hφ _

theorem shift_jointly_continuous {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (h : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2) (c : ℂ) :
    Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => φ (p.1 + c) p.2 :=
  h.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)

theorem shift_differentiable {f : ℂ → ℂ} (h : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (fun s => f (s + c)) :=
  h.comp (differentiable_id.add_const c)

theorem mem_shiftSet {O : Set ℂ} (c s : ℂ) : s ∈ (Homeomorph.addRight c) ⁻¹' O ↔ s + c ∈ O := Iff.rfl

theorem shift_isOpen {O : Set ℂ} (hO : IsOpen O) (c : ℂ) : IsOpen ((Homeomorph.addRight c) ⁻¹' O) :=
  hO.preimage (Homeomorph.addRight c).continuous

theorem shift_isPreconnected {O : Set ℂ} (hO : IsPreconnected O) (c : ℂ) :
    IsPreconnected ((Homeomorph.addRight c) ⁻¹' O) :=
  ((Homeomorph.addRight c).isPreconnected_preimage).2 hO

theorem shift_axis_subset {O : Set ℂ} (hO : {s : ℂ | s.re = 0} ⊆ O) (τ : ℝ) :
    {s : ℂ | s.re = 0} ⊆ (Homeomorph.addRight ((τ : ℂ) * Complex.I)) ⁻¹' O := by
  intro s hs
  rw [mem_shiftSet]
  apply hO
  simp only [Set.mem_setOf_eq] at hs ⊢
  simp [Complex.add_re, hs]

theorem shift_halfPlane_subset {O : Set ℂ} (hO : {s : ℂ | 1 / 2 < s.re} ⊆ O) (τ : ℝ) :
    {s : ℂ | 1 / 2 < s.re} ⊆ (Homeomorph.addRight ((τ : ℂ) * Complex.I)) ⁻¹' O := by
  intro s hs
  rw [mem_shiftSet]
  apply hO
  simp only [Set.mem_setOf_eq] at hs ⊢
  simpa [Complex.add_re] using hs

theorem shift_analyticOnNhd {O : Set ℂ} {f : ℂ → ℂ} (h : AnalyticOnNhd ℂ f O) (c : ℂ) :
    AnalyticOnNhd ℂ (fun s => f (s + c)) ((Homeomorph.addRight c) ⁻¹' O) := by
  have h1 : AnalyticOnNhd ℂ (fun s : ℂ => s + c) ((Homeomorph.addRight c) ⁻¹' O) :=
    fun s _ => (analyticAt_id.add analyticAt_const)
  exact h.comp h1 fun s hs => hs

theorem shift_continuousOn {O : Set ℂ} {N : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (h : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => N p.1 p.2) (O ×ˢ univ)) (c : ℂ) :
    ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => N (p.1 + c) p.2)
      (((Homeomorph.addRight c) ⁻¹' O) ×ˢ univ) := by
  refine h.comp ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn ?_
  rintro ⟨s, g⟩ ⟨hs, -⟩
  exact ⟨hs, mem_univ _⟩

end Shift

theorem final_bound {X c R Λ B₁ B₂ d₁ Q Q' : ℝ} {A : ℕ} (hc : 0 < c) (hΛ : 1 ≤ Λ) (hd₁ : 0 ≤ d₁)
    (hQ : 0 ≤ Q) (hQ' : Q ≤ Q')
    (h : X ≤ c * ((|R| + 1) * 1 + Real.sqrt 1 * B₁ + B₂)) (hB₁ : B₁ ≤ d₁ * Λ ^ A) (hB₂ : B₂ ≤ Q * Λ ^ A) :
    X ≤ c * (1 + d₁ + Q') * (|R| + 1) * Λ ^ A := by
  rw [Real.sqrt_one, one_mul, mul_one] at h
  have hΛA : 1 ≤ Λ ^ A := one_le_pow₀ hΛ
  have hΛA0 : 0 ≤ Λ ^ A := le_trans zero_le_one hΛA
  have hR : 1 ≤ |R| + 1 := by linarith [abs_nonneg R]
  have hR0 : 0 ≤ |R| + 1 := le_trans zero_le_one hR
  have h1 : (|R| + 1) + B₁ + B₂ ≤ (1 + d₁ + Q') * (|R| + 1) * Λ ^ A := by
    have e1 : (|R| + 1) ≤ 1 * (|R| + 1) * Λ ^ A := by
      rw [one_mul]; exact le_mul_of_one_le_right hR0 hΛA
    have e2 : B₁ ≤ d₁ * (|R| + 1) * Λ ^ A := by
      refine hB₁.trans ?_
      rw [mul_assoc, mul_comm (|R| + 1), ← mul_assoc]
      exact le_mul_of_one_le_right (mul_nonneg hd₁ hΛA0) hR
    have e3 : B₂ ≤ Q' * (|R| + 1) * Λ ^ A := by
      refine hB₂.trans ?_
      have e4 : Q * Λ ^ A ≤ Q' * Λ ^ A := mul_le_mul_of_nonneg_right hQ' hΛA0
      refine e4.trans ?_
      rw [mul_assoc, mul_comm (|R| + 1), ← mul_assoc]
      exact le_mul_of_one_le_right (mul_nonneg (hQ.trans hQ') hΛA0) hR
    have hexp : (1 + d₁ + Q') * (|R| + 1) * Λ ^ A =
        1 * (|R| + 1) * Λ ^ A + d₁ * (|R| + 1) * Λ ^ A + Q' * (|R| + 1) * Λ ^ A := by ring
    rw [hexp]; linarith
  calc X ≤ c * ((|R| + 1) + B₁ + B₂) := h
    _ ≤ c * ((1 + d₁ + Q') * (|R| + 1) * Λ ^ A) := mul_le_mul_of_nonneg_left h1 hc.le
    _ = _ := by ring

open NumberField.AdelicLevel NumberField.AdelicBox
open scoped NNReal

theorem main
    (K : Type) [Field K] [NumberField K] [DecidableEq (IsDedekindDomain.HeightOneSpectrum (𝓞 K))]
    (N : Ideal (𝓞 K)) (_hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιE : Type)
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
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
      (uμ uν : ιE → InfinitePlace K → ℂ) (aμ aν : ιE → InfinitePlace K → ℤ)
      (_hμA : ∀ (e : ιE) (w : InfinitePlace K), LanglandsTunnell.Converse.IsArchCompAt K (μ e) w (uμ e w) (aμ e w))
      (_hνA : ∀ (e : ιE) (w : InfinitePlace K), LanglandsTunnell.Converse.IsArchCompAt K (ν e) w (uν e w) (aν e w))
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
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g)),
    ∀ (α β : ℝ), 0 < α → α < β → ∀ (ΦK : Set (AdelicGL2 (𝓞 K) K)),
    ∃ (c : ℝ) (A : ℕ) (R₀ : ℝ), 0 < c ∧
      ∀ (e : ιE) (i : Fin (nE e)) (t : ℝ),
        (μ e = ν e ∧ t ≠ 0 ∨ ∃ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z ≠ ν e z) →
        ∀ (R : ℝ), R₀ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 K) K =>
          ‖@AutomorphicForm.lambdaT _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
          (fun q => AutomorphicForm.unipotentGL2 q)
          (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (EE e i ((t : ℂ) * Complex.I)) x‖ ^ 2)
        (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
      ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
          ‖@AutomorphicForm.lambdaT _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
          (fun q => AutomorphicForm.unipotentGL2 q)
          (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (EE e i ((t : ℂ) * Complex.I)) x‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤
        c * (|R| + 1) * (1 + ∑ w : InfinitePlace K, ‖2 * (t : ℂ) * Complex.I + (uμ e w - uν e w)‖) ^ A := by
  intro αm hαm ιE μ ν hμ hν hμic hνic hμc hνc nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon
    uμ uν aμ aν hμA hνA OE EE NE hEE α β hα hαβ ΦK
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  have hαn : ∀ x, ((αm x : ℝˣ) : ℝ) = ideleNorm K x := fun x => rfl

  obtain ⟨A₁, d₁, hd₁, hS₁⟩ :=
    (AutomorphicForm.exists_forall_integral_maximalCompact_norm_sq_deriv_axis_continuation_weylIntertwiningIntegral_le_and_norm_sq_sub_le_of_flat_of_ne_bot
      K N _hN tysK) hαm ιE μ ν hμ hν hμic hνic hμc hνc nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty
      hφEon uμ uν aμ aν hμA hνA OE EE NE hEE

  set uν' : ιE → InfinitePlace K → ℂ := fun e w => if μ e = ν e then uμ e w else uν e w with huν'
  set aν' : ιE → InfinitePlace K → ℤ := fun e w => if μ e = ν e then aμ e w else aν e w with haν'
  have hνA' : ∀ (e : ιE) (w : InfinitePlace K),
      LanglandsTunnell.Converse.IsArchCompAt K (ν e) w (uν' e w) (aν' e w) := by
    intro e w
    by_cases h : μ e = ν e
    · simp only [huν', haν', h, if_true]
      rw [← h]; exact hμA e w
    · simp only [huν', haν', h, if_false]
      exact hνA e w
  obtain ⟨A₂, d₂, hd₂, hS₂⟩ :=
    (AutomorphicForm.exists_forall_integral_maximalCompact_norm_sq_deriv_axis_continuation_weylIntertwiningIntegral_le_and_norm_sq_sub_le_of_flat_of_ne_bot
      K N _hN tysK) hαm ιE μ ν hμ hν hμic hνic hμc hνc nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty
      hφEon uμ uν' aμ aν' hμA hνA' OE EE NE hEE

  obtain ⟨c, hc, R₀, hMS⟩ :=
    (AutomorphicForm.exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_of_flat_of_eLpNorm_deriv_le
      K α β hα hαβ ΦK N _hN) hαm

  set n : ℝ := (Fintype.card (InfinitePlace K) : ℝ) with hn
  have hn0 : 0 ≤ n := by rw [hn]; positivity
  set Q₁ : ℝ := d₁ * (1 + 4 * n) ^ A₁ with hQ₁
  set Q₂ : ℝ := d₂ * (1 + 2 * n) ^ A₂ with hQ₂
  have hQ₁0 : 0 ≤ Q₁ := by rw [hQ₁]; positivity
  have hQ₂0 : 0 ≤ Q₂ := by rw [hQ₂]; positivity
  refine ⟨c * (1 + d₁ + (Q₁ + Q₂)), A₁, R₀, by positivity, ?_⟩
  intro e i t hpair R hR

  set cK : ℂ := ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ with hcK
  set Λ : ℝ → ℝ := fun σ => 1 + ∑ w : InfinitePlace K, ‖2 * (σ : ℂ) * Complex.I + (uμ e w - uν e w)‖ with hΛ
  have hΛ1 : ∀ σ, 1 ≤ Λ σ := fun σ => one_le_gauge K _ σ
  have hΛ0 : ∀ σ, 0 ≤ Λ σ := fun σ => le_trans zero_le_one (hΛ1 σ)
  obtain ⟨hO, hOpc, hOax, hOhp, hEa, hNa, hEc, hNc, hEeq, hNeq⟩ := hEE e i

  have hP : ∫ k, ‖φE e i 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) = 1 := by
    have h := hφEon e i i
    rw [if_pos rfl] at h
    exact integral_norm_sq_eq_of (by exact_mod_cast h)

  have hB₁sqrt : ∀ σ : ℝ, Real.sqrt (∫ k, ‖cK * deriv (fun s : ℂ => NE e i s (k : AdelicGL2 (𝓞 K) K)) ((σ : ℂ) * Complex.I)‖ ^ 2
      ∂(maximalCompactHaar K)) ≤ d₁ * Λ σ ^ A₁ := fun σ =>
    sqrt_integral_le (mul_nonneg hd₁ (pow_nonneg (hΛ0 σ) _)) (hS₁ e i σ σ).1

  rcases hpair with ⟨hdiag, ht⟩ | ⟨z, hz, hne⟩
  ·

    have huν'e : ∀ w, uν' e w = uμ e w := fun w => by simp only [huν', hdiag, if_true]
    have hB₂in : ∀ σ : ℝ, |σ| ≤ 1 → Real.sqrt (∫ k, ‖cK * deriv (fun s : ℂ => NE e i s (k : AdelicGL2 (𝓞 K) K)) ((σ : ℂ) * Complex.I)‖ ^ 2
        ∂(maximalCompactHaar K)) ≤ d₂ * (1 + 2 * n) ^ A₂ := by
      intro σ hσ
      have h1 := (hS₂ e i σ σ).1
      have hg : (1 + ∑ w : InfinitePlace K, ‖2 * (σ : ℂ) * Complex.I + (uμ e w - uν' e w)‖) ≤ 1 + 2 * n := by
        simp_rw [huν'e]
        exact gauge_diag_le K (uμ e) hσ
      have hg0 : 0 ≤ (1 + ∑ w : InfinitePlace K, ‖2 * (σ : ℂ) * Complex.I + (uμ e w - uν' e w)‖) :=
        le_trans zero_le_one (one_le_gauge K _ σ)
      refine (sqrt_integral_le (mul_nonneg hd₂ (pow_nonneg hg0 _)) h1).trans ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0 hg _) hd₂

    have hreg := (AutomorphicForm.continuous_and_hasDerivAt_axis_continuation_weylIntertwiningIntegral_pairings_of_flat K)
      hαm (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e)
      (φE e i) (hφE e i) (hφEK e i) (hφEf e i) (hφEjc e i) (hφEhol e i) (hφEKu e i) (hφEflat e i)
      (φE e i) (hφE e i) (hφEK e i) (hφEf e i) (hφEjc e i) (hφEhol e i) (hφEKu e i) (hφEflat e i)
      (OE e i) (EE e i) (NE e i) (hEE e i) (OE e i) (EE e i) (NE e i) (hEE e i)
    obtain ⟨_hUc, _hVc, _hQc, _hU'c, _hV'c, hdU, _hdV, hbd⟩ := hreg
    set U : ℝ → ℂ := fun σ =>
        ∫ k, φE e i ((σ : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj ((fun g => cK * NE e i ((σ : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) with hUdef
    set U' : ℝ → ℂ := fun σ =>
        ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) *
          conj (cK * (Complex.I * deriv (fun s : ℂ => NE e i s (k : AdelicGL2 (𝓞 K) K)) ((σ : ℂ) * Complex.I)))
            ∂(maximalCompactHaar K) with hU'def
    have hC : ∀ σ ∈ Set.Icc (-1 : ℝ) 1, ‖U' σ‖ ≤ Q₂ := by
      intro σ hσ
      have hσ1 : |σ| ≤ 1 := abs_le.mpr ⟨by linarith [hσ.1], hσ.2⟩
      have h1 : ‖U' σ‖ ≤ Real.sqrt (∫ k, ‖φE e i 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K)) *
          Real.sqrt (∫ k, ‖cK * deriv (fun s : ℂ => NE e i s (k : AdelicGL2 (𝓞 K) K)) ((σ : ℂ) * Complex.I)‖ ^ 2
            ∂(maximalCompactHaar K)) := (hbd σ).2.2.2.1
      rw [hP, Real.sqrt_one, one_mul] at h1
      exact h1.trans (hB₂in σ hσ1)
    have hlip : ∀ s : ℝ, |s| ≤ 1 →
        ‖(∫ k, φE e i ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
              conj ((fun g => cK * NE e i ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) -
          (∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) *
              conj ((fun g => cK * NE e i 0 g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))‖ ≤ Q₂ * |s| := by
      intro s hs
      have hMV := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := U) (f' := U')
        (fun x _ => (hdU x).hasDerivWithinAt) hC (convex_Icc (-1 : ℝ) 1)
        (show (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 by constructor <;> norm_num)
        (show s ∈ Set.Icc (-1 : ℝ) 1 from ⟨by linarith [(abs_le.mp hs).1], (abs_le.mp hs).2⟩)
      have hU0 : U 0 = ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) *
          conj ((fun g => cK * NE e i 0 g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
        simp only [hUdef, Complex.ofReal_zero, zero_mul]
      have hUs : U s = ∫ k, φE e i ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj ((fun g => cK * NE e i ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := rfl
      rw [← hUs, ← hU0]
      simpa [Real.norm_eq_abs] using hMV

    have hderiv : eLpNorm (fun k : adelicMaximalCompact K =>
          cK * deriv (fun s : ℂ => NE e i s (k : AdelicGL2 (𝓞 K) K)) ((t : ℂ) * Complex.I))
        2 (maximalCompactHaar K) ≤ ENNReal.ofReal (d₁ * Λ t ^ A₁) :=
      eLpNorm_deriv_le K hO (NE e i) hNa hNc (axis_mem hOax t) cK (mul_nonneg hd₁ (pow_nonneg (hΛ0 t) _))
        (hS₁ e i t t).1

    have hres := hMS (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (Or.inl hdiag)
      (φE e i) (hφE e i) (hφEK e i) (hφEf e i) (hφEjc e i) (hφEhol e i) (hφEKu e i) (hφEflat e i) (hφElev e i)
      (OE e i) (EE e i) (NE e i) (hEE e i) t ht R hR (d₁ * Λ t ^ A₁) Q₂
      (mul_nonneg hd₁ (pow_nonneg (hΛ0 t) _)) hQ₂0 hderiv hlip
    refine ⟨hres.1, ?_⟩
    have h2 := hres.2
    rw [hP] at h2
    exact final_bound (A := A₁) hc (hΛ1 t) hd₁ hQ₂0 (show Q₂ ≤ Q₁ + Q₂ by linarith) h2 le_rfl
      (show Q₂ ≤ Q₂ * Λ t ^ A₁ from le_mul_of_one_le_right hQ₂0 (one_le_pow₀ (hΛ1 t)))
  ·

    set τ : ℝ := t - 1 with hτ
    set τc : ℂ := (τ : ℂ) * Complex.I with hτc
    set μ' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := μ e * normPowChar K τ with hμ'
    set ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := ν e * normPowChar K (-τ) with hν'
    set φ' : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun s g => φE e i (s + τc) g with hφ'
    set O' : Set ℂ := (Homeomorph.addRight τc) ⁻¹' OE e i with hO'
    set E' : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun s g => EE e i (s + τc) g with hE'
    set N' : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun s g => NE e i (s + τc) g with hN'

    have hμ'u : IsUnitaryChar (𝓞 K) K μ' := isUnitaryChar_mul K (hμ e) (isUnitaryChar_normPowChar K τ)
    have hν'u : IsUnitaryChar (𝓞 K) K ν' := isUnitaryChar_mul K (hν e) (isUnitaryChar_normPowChar K (-τ))
    have hμ'ic : IsIdeleClassChar (𝓞 K) K μ' := isIdeleClassChar_mul K (hμic e) (isIdeleClassChar_normPowChar K τ)
    have hν'ic : IsIdeleClassChar (𝓞 K) K ν' := isIdeleClassChar_mul K (hνic e) (isIdeleClassChar_normPowChar K (-τ))
    have hμ'c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ) := continuous_mul_normPowChar K (hμc e) τ
    have hν'c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ) := continuous_mul_normPowChar K (hνc e) (-τ)
    have hpair' : μ' = ν' ∨ ∃ z ∈ NumberField.TateGlobal.normOneIdeles K, μ' z ≠ ν' z := by
      refine Or.inr ⟨z, hz, ?_⟩
      simp only [hμ', hν', MonoidHom.mul_apply, normPowChar_apply_of_mem_normOneIdeles K _ hz, mul_one]
      exact hne

    have hφ'1 : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ' αm hαm s) (etaSnd ν' αm hαm s) (φ' s) := fun s =>
      shift_isInducedSection αm hαm hαn (hφE e i) τ s
    have hφ'K : ∀ s, IsArchKFinite K (φ' s) := fun s => hφEK e i (s + τc)
    have hφ'f : ∀ s, IsKfSmooth K (φ' s) := fun s => hφEf e i (s + τc)
    have hφ'jc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ' p.1 p.2) := shift_jointly_continuous (hφEjc e i) τc
    have hφ'hol : ∀ g, Differentiable ℂ (fun s => φ' s g) := fun g => shift_differentiable (hφEhol e i g) τc
    have hφ'Ku : ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φ' s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W := by
      intro w
      obtain ⟨W, hW, hmem⟩ := hφEKu e i w
      exact ⟨W, hW, fun s g => hmem (s + τc) g⟩
    have hφ'flat : ∀ (s : ℂ) (k : adelicMaximalCompact K), φ' s (k : AdelicGL2 (𝓞 K) K) = φ' 0 (k : AdelicGL2 (𝓞 K) K) := by
      intro s k
      simp only [hφ']
      rw [hφEflat e i (s + τc) k, hφEflat e i (0 + τc) k]
    have hφ'lev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ' s (g * u) = φ' s g :=
      fun s g u hu => hφElev e i (s + τc) g u hu

    have hre : ∀ s : ℂ, (s + τc).re = s.re := fun s => by simp [hτc, Complex.add_re]
    have hE'data :
        IsOpen O' ∧ IsPreconnected O' ∧ {s : ℂ | s.re = 0} ⊆ O' ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O' ∧
        (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => E' s g) O') ∧
        (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => N' s g) O') ∧
        ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => E' p.1 p.2) (O' ×ˢ Set.univ) ∧
        ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => N' p.1 p.2) (O' ×ˢ Set.univ) ∧
        (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
          E' s g = φ' s g + ∑' ξ : K, φ' s (adelicWeyl (𝓞 K) K
            * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
        (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
          N' s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φ' s) g) := by
      refine ⟨shift_isOpen hO τc, shift_isPreconnected hOpc τc, shift_axis_subset hOax τ,
        shift_halfPlane_subset hOhp τ, fun g => shift_analyticOnNhd (hEa g) τc,
        fun g => shift_analyticOnNhd (hNa g) τc, shift_continuousOn hEc τc, shift_continuousOn hNc τc,
        fun s hs g => ?_, fun s hs g => ?_⟩
      · exact hEeq (s + τc) (by rw [hre]; exact hs) g
      · exact hNeq (s + τc) (by rw [hre]; exact hs) g
    have hO'o : IsOpen O' := hE'data.1
    have hO'ax : {s : ℂ | s.re = 0} ⊆ O' := hE'data.2.2.1
    have hN'a : ∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => N' s g) O' := hE'data.2.2.2.2.2.1
    have hN'c : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => N' p.1 p.2) (O' ×ˢ Set.univ) :=
      hE'data.2.2.2.2.2.2.2.1

    have hderiv_shift : ∀ (σ : ℝ) (k : AdelicGL2 (𝓞 K) K),
        deriv (fun s : ℂ => N' s k) ((σ : ℂ) * Complex.I) =
          deriv (fun s : ℂ => NE e i s k) (((σ + τ : ℝ) : ℂ) * Complex.I) := by
      intro σ k
      have h1 : deriv (fun s : ℂ => N' s k) ((σ : ℂ) * Complex.I) =
          deriv (fun s : ℂ => NE e i s k) ((σ : ℂ) * Complex.I + τc) := by
        simp only [hN']
        exact deriv_comp_add_const (fun s : ℂ => NE e i s k) τc ((σ : ℂ) * Complex.I)
      rw [h1]; congr 1; simp only [hτc]; push_cast; ring

    have hP' : ∫ k, ‖φ' 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) = 1 := by
      have : ∀ k : adelicMaximalCompact K, φ' 0 (k : AdelicGL2 (𝓞 K) K) = φE e i 0 (k : AdelicGL2 (𝓞 K) K) :=
        fun k => by simp only [hφ']; exact hφEflat e i (0 + τc) k
      simp_rw [this]; exact hP

    have hreg := (AutomorphicForm.continuous_and_hasDerivAt_axis_continuation_weylIntertwiningIntegral_pairings_of_flat K)
      hαm μ' ν' hμ'u hν'u hμ'ic hν'ic hμ'c hν'c
      φ' hφ'1 hφ'K hφ'f hφ'jc hφ'hol hφ'Ku hφ'flat
      φ' hφ'1 hφ'K hφ'f hφ'jc hφ'hol hφ'Ku hφ'flat
      O' E' N' hE'data O' E' N' hE'data
    obtain ⟨_hUc, _hVc, _hQc, _hU'c, _hV'c, hdU, _hdV, hbd⟩ := hreg
    set U : ℝ → ℂ := fun σ =>
        ∫ k, φ' ((σ : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj ((fun g => cK * N' ((σ : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) with hUdef
    set U' : ℝ → ℂ := fun σ =>
        ∫ k, φ' 0 (k : AdelicGL2 (𝓞 K) K) *
          conj (cK * (Complex.I * deriv (fun s : ℂ => N' s (k : AdelicGL2 (𝓞 K) K)) ((σ : ℂ) * Complex.I)))
            ∂(maximalCompactHaar K) with hU'def

    have hC : ∀ σ ∈ Set.Icc (-1 : ℝ) 1, ‖U' σ‖ ≤ Q₁ * Λ t ^ A₁ := by
      intro σ hσ
      have h1 : ‖U' σ‖ ≤ Real.sqrt (∫ k, ‖φ' 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K)) *
          Real.sqrt (∫ k, ‖cK * deriv (fun s : ℂ => N' s (k : AdelicGL2 (𝓞 K) K)) ((σ : ℂ) * Complex.I)‖ ^ 2
            ∂(maximalCompactHaar K)) := (hbd σ).2.2.2.1
      rw [hP', Real.sqrt_one, one_mul] at h1
      simp_rw [hderiv_shift σ] at h1
      have h2 := hB₁sqrt (σ + τ)
      have h3 : Λ (σ + τ) ≤ Λ t + 2 * n * 2 := by
        have := gauge_le_gauge_add K (fun w => uμ e w - uν e w) (σ + τ) t
        have h4 : |σ + τ - t| ≤ 2 := by
          rw [hτ]; rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
        have h5 : 2 * (Fintype.card (InfinitePlace K) : ℝ) * |σ + τ - t| ≤ 2 * n * 2 := by
          rw [← hn]; exact mul_le_mul_of_nonneg_left h4 (by positivity)
        simp only [hΛ] at this ⊢
        linarith
      have h6 : Λ (σ + τ) ≤ (1 + 4 * n) * Λ t := by nlinarith [hΛ1 t]
      have h7 : d₁ * Λ (σ + τ) ^ A₁ ≤ Q₁ * Λ t ^ A₁ := by
        rw [hQ₁, mul_assoc, ← mul_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hΛ0 _) h6 _) hd₁
      exact h1.trans (h2.trans h7)
    have hlip : ∀ s : ℝ, |s| ≤ 1 →
        ‖(∫ k, φ' ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
              conj ((fun g => cK * N' ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) -
          (∫ k, φ' 0 (k : AdelicGL2 (𝓞 K) K) *
              conj ((fun g => cK * N' 0 g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))‖ ≤ (Q₁ * Λ t ^ A₁) * |s| := by
      intro s hs
      have hMV := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := U) (f' := U')
        (fun x _ => (hdU x).hasDerivWithinAt) hC (convex_Icc (-1 : ℝ) 1)
        (show (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 by constructor <;> norm_num)
        (show s ∈ Set.Icc (-1 : ℝ) 1 from ⟨by linarith [(abs_le.mp hs).1], (abs_le.mp hs).2⟩)
      have hU0 : U 0 = ∫ k, φ' 0 (k : AdelicGL2 (𝓞 K) K) *
          conj ((fun g => cK * N' 0 g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
        simp only [hUdef, Complex.ofReal_zero, zero_mul]
      have hUs : U s = ∫ k, φ' ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj ((fun g => cK * N' ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := rfl
      rw [← hUs, ← hU0]
      simpa [Real.norm_eq_abs] using hMV

    have hderiv : eLpNorm (fun k : adelicMaximalCompact K =>
          cK * deriv (fun s : ℂ => N' s (k : AdelicGL2 (𝓞 K) K)) (((1 : ℝ) : ℂ) * Complex.I))
        2 (maximalCompactHaar K) ≤ ENNReal.ofReal (d₁ * Λ t ^ A₁) := by
      refine eLpNorm_deriv_le K hO'o N' hN'a hN'c (axis_mem hO'ax 1) cK (mul_nonneg hd₁ (pow_nonneg (hΛ0 t) A₁)) ?_
      simp_rw [hderiv_shift 1]
      have : (1 : ℝ) + τ = t := by rw [hτ]; ring
      rw [this]
      exact (hS₁ e i t t).1

    have hres := hMS μ' ν' hμ'u hν'u hμ'ic hν'ic hμ'c hν'c hpair'
      φ' hφ'1 hφ'K hφ'f hφ'jc hφ'hol hφ'Ku hφ'flat hφ'lev
      O' E' N' hE'data 1 one_ne_zero R hR (d₁ * Λ t ^ A₁) (Q₁ * Λ t ^ A₁)
      (mul_nonneg hd₁ (pow_nonneg (hΛ0 t) _)) (mul_nonneg hQ₁0 (pow_nonneg (hΛ0 t) _)) hderiv hlip

    have hE'1 : E' (((1 : ℝ) : ℂ) * Complex.I) = EE e i ((t : ℂ) * Complex.I) := by
      funext g
      simp only [hE', hτc, hτ]
      congr 1; push_cast; ring
    rw [hE'1, hP'] at hres
    refine ⟨hres.1, ?_⟩
    exact final_bound (A := A₁) hc (hΛ1 t) hd₁ hQ₁0 (show Q₁ ≤ Q₁ + Q₂ by linarith) hres.2 le_rfl le_rfl

end R4MsL2Fam

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open AutomorphicForm
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (N : Ideal (𝓞 K)) (_hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιE : Type)
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
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
      (uμ uν : ιE → InfinitePlace K → ℂ) (aμ aν : ιE → InfinitePlace K → ℤ)
      (_hμA : ∀ (e : ιE) (w : InfinitePlace K), LanglandsTunnell.Converse.IsArchCompAt K (μ e) w (uμ e w) (aμ e w))
      (_hνA : ∀ (e : ιE) (w : InfinitePlace K), LanglandsTunnell.Converse.IsArchCompAt K (ν e) w (uν e w) (aν e w))
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
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g)),
    ∀ (α β : ℝ), 0 < α → α < β → ∀ (ΦK : Set (AdelicGL2 (𝓞 K) K)),
    ∃ (c : ℝ) (A : ℕ) (R₀ : ℝ), 0 < c ∧
      ∀ (e : ιE) (i : Fin (nE e)) (t : ℝ),
        (μ e = ν e ∧ t ≠ 0 ∨ ∃ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z ≠ ν e z) →
        ∀ (R : ℝ), R₀ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 K) K =>
          ‖@AutomorphicForm.lambdaT _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
          (fun q => AutomorphicForm.unipotentGL2 q)
          (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (EE e i ((t : ℂ) * Complex.I)) x‖ ^ 2)
        (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
      ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
          ‖@AutomorphicForm.lambdaT _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
          (fun q => AutomorphicForm.unipotentGL2 q)
          (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (EE e i ((t : ℂ) * Complex.I)) x‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤
        c * (|R| + 1) * (1 + ∑ w : InfinitePlace K, ‖2 * (t : ℂ) * Complex.I + (uμ e w - uν e w)‖) ^ A :=
  R4MsL2Fam.main K N _hN tysK

end
end S_AutomorphicForm_exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_mul_pow_of_eq_or_exists_normOneIdeles_of_isArchCompAt_of_ne_bot
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_mul_pow_of_eq_or_exists_normOneIdeles_of_isArchCompAt_of_ne_bot (solution)
