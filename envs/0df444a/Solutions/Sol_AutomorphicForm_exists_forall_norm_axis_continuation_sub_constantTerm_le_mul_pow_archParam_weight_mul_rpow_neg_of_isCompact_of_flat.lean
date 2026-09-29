-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/22e69ebd-ee0a-52ab-abbf-ddee505cde29

import Theorems.Thm_AutomorphicForm_exists_forall_exists_entire_eulerProduct_mul_eq_bruhatEisenstein_sub_constantTerm_norm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
import Theorems.Thm_AutomorphicForm_exists_forall_exists_entire_mul_eulerProduct_eq_and_ne_zero_and_norm_le_mul_pow_archParam_weight_mul_norm_of_isInducedSection_principalLevel
import Theorems.Thm_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Ws2
namespace U1

open MeasureTheory Set NumberField IsDedekindDomain Filter Metric
open AutomorphicForm NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section Continuation

theorem eqOn_of_eq_on_re_gt_one {O : Set ℂ} (hOc : IsPreconnected O)
    (hOhalf : {s : ℂ | 1 / 2 < s.re} ⊆ O) {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f O) (hg : AnalyticOnNhd ℂ g O)
    (h : ∀ s : ℂ, 1 < s.re → f s = g s) : EqOn f g O := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have h2' : (2 : ℂ) ∈ O := hOhalf (by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num)
  have hev : f =ᶠ[𝓝 (2 : ℂ)] g :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds h2) fun s hs => h s hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hOc h2' hev

theorem eqOn_zero_of_eq_zero_on_re_gt_one {O : Set ℂ} (hOc : IsPreconnected O)
    (hOhalf : {s : ℂ | 1 / 2 < s.re} ⊆ O) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f O)
    (h : ∀ s : ℂ, 1 < s.re → f s = 0) : ∀ s ∈ O, f s = 0 :=
  fun s hs => eqOn_of_eq_on_re_gt_one hOc hOhalf hf analyticOnNhd_const h hs

end Continuation

section ConstantTerm

variable (F : Type) [Field F] [NumberField F]

scoped instance isFiniteMeasure_cond_adelicBox :
    IsFiniteMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  haveI := isProbabilityMeasure_cond_adelicBox F
  infer_instance

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

theorem constantTerm_zero_fun (F : Type) [Field F] [NumberField F] (h : AdelicGL2 (𝓞 F) F) :
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      (fun t => unipotentGL2 t) (fun _ : AdelicGL2 (𝓞 F) F => (0 : ℂ)) h = 0 := by
  unfold constantTerm constantTermIntegrand
  simp

end Ws2.U1
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat.Ws2 P2MW.S_AutomorphicForm_exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat.Ws2.U1"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat.Ws2"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat.Ws2 P2MW.S_AutomorphicForm_exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat.Ws2.U1"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm Ws2.U1

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
    (Ω : Set (AdelicGL2 (𝓞 K) K)) (hΩ : IsCompact Ω) (c' : ℝ) (hc' : 0 < c') (N' : ℕ)
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ s g = ψf s g + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) g))
      (t : ℝ) (b : ↥(adelicBorel (𝓞 K) K)) (ω : AdelicGL2 (𝓞 K) K),
      ω ∈ Ω → c' ≤ (((αm (borelDiagFst b) : ℝˣ) : ℝ) / ((αm (borelDiagSnd b) : ℝˣ) : ℝ)) →
      ‖Eψ ((t : ℂ) * Complex.I) ((b : AdelicGL2 (𝓞 K) K) * ω) -
          AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
          (fun u => AutomorphicForm.unipotentGL2 u) (Eψ ((t : ℂ) * Complex.I)) ((b : AdelicGL2 (𝓞 K) K) * ω)‖ ≤
        C * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A *
          (((αm (borelDiagFst b) : ℝˣ) : ℝ) / ((αm (borelDiagSnd b) : ℝˣ) : ℝ)) ^ (-(N' : ℝ)) := by
  intro αm
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K

  obtain ⟨S, C₁, A₁, hSK, hC₁, H1⟩ :=
    AutomorphicForm.exists_forall_exists_entire_eulerProduct_mul_eq_bruhatEisenstein_sub_constantTerm_norm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
      K SK ξK hξc hξt N hN tysK w hξw Ω hΩ c' hc' N'
  obtain ⟨C₂, A₂, hC₂, H2⟩ :=
    AutomorphicForm.exists_forall_exists_entire_mul_eulerProduct_eq_and_ne_zero_and_norm_le_mul_pow_archParam_weight_mul_norm_of_isInducedSection_principalLevel K SK N hN S hSK
  refine ⟨C₁ * C₂, A₁ + A₂, mul_pos hC₁ hC₂, ?_⟩
  intro hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν mμ mν hmμ hmν ψf hψf hψfK hψff hψfjc hψfhol hψfKu
    hψfflat hψflev hψfty hψfn Oψ Eψ Nψ hEψ t b ω hω hb
  obtain ⟨hO, hOc, hax, hhalf, hEa, hNa, hEjc, hNjc, hE, hN⟩ := hEψ
  set x : AdelicGL2 (𝓞 K) K := (b : AdelicGL2 (𝓞 K) K) * ω with hx
  set D : ℝ := 1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ)) with hD
  set H : ℝ := ((αm (borelDiagFst b) : ℝˣ) : ℝ) / ((αm (borelDiagSnd b) : ℝˣ) : ℝ) with hH
  have hD0 : 0 ≤ D := by
    have : 0 ≤ ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ)) :=
      Finset.sum_nonneg fun v _ => by positivity
    simp only [hD]; linarith
  have hHpos : 0 < H := lt_of_lt_of_le hc' hb
  have hit : ((t : ℂ) * Complex.I) ∈ Oψ := hax (by simp)

  have hCTa := analyticOnNhd_constantTerm hO hEa hEjc x
  have hWa : AnalyticOnNhd ℂ (fun s => Eψ s x -
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
        (fun u => unipotentGL2 u) (Eψ s) x) Oψ := (hEa x).sub hCTa

  have hϖ : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (uniformizerUnit K v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ) :=
    fun v => valued_uniformizerUnit K v
  by_cases hzero : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ψf s g = 0
  ·
    have hE0 : ∀ g : AdelicGL2 (𝓞 K) K, ∀ s ∈ Oψ, Eψ s g = 0 := by
      intro g
      refine eqOn_zero_of_eq_zero_on_re_gt_one hOc hhalf (hEa g) ?_
      intro s hs
      rw [hE s (by linarith) g]
      simp [hzero]
    have hfun : Eψ ((t : ℂ) * Complex.I) = fun _ => (0 : ℂ) := funext fun g => hE0 g _ hit
    rw [hfun, constantTerm_zero_fun]
    simp only [sub_zero, norm_zero]
    positivity
  push Not at hzero
  obtain ⟨s₀, g₀, hne⟩ := hzero
  have hφ0 : ψf s₀ ≠ 0 := fun h => hne (by rw [h]; rfl)
  obtain ⟨V, hVd, hVE, hVb⟩ := H1 hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν mμ mν hmμ hmν ψf hψf hψfK
    hψff hψfjc hψfhol hψfKu hψfflat hψflev hψfty hψfn (fun v => uniformizerUnit K v) hϖ
  obtain ⟨G, p, hGd, hpd, hGp, hGt⟩ := H2 hαm μ ν hμ hν hμic hνic hμc hνc τμ τν hτμ hτν mμ mν hmμ hmν s₀ (ψf s₀)
    (hψf s₀) hφ0 (hψflev s₀) (fun v => uniformizerUnit K v) hϖ
  obtain ⟨hG0, hpG⟩ := hGt t

  have hGa : AnalyticOnNhd ℂ G Oψ := (hGd.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hpa : AnalyticOnNhd ℂ p Oψ := (hpd.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hVa : AnalyticOnNhd ℂ (fun s => V s x) Oψ :=
    ((hVd x).differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have key : Set.EqOn (fun s => (Eψ s x -
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
        (fun u => unipotentGL2 u) (Eψ s) x) * G s) (fun s => p s * V s x) Oψ := by
    refine eqOn_of_eq_on_re_gt_one hOc hhalf (hWa.mul hGa) (hpa.mul hVa) ?_
    intro s hs1
    have hsE : Eψ s = fun h => ψf s h + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K *
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * h) := funext fun h => hE s (by linarith) h
    have h1 := hVE s x hs1
    have h2 := hGp s hs1
    rw [hsE]
    simp only at h1 h2 ⊢
    rw [← h1, ← h2]
    ring
  have hkey := key hit
  simp only at hkey

  have hVn := hVb t b ω hω hb
  have hnorm : ‖Eψ ((t : ℂ) * Complex.I) x -
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
        (fun u => unipotentGL2 u) (Eψ ((t : ℂ) * Complex.I)) x‖ * ‖G ((t : ℂ) * Complex.I)‖
      = ‖p ((t : ℂ) * Complex.I)‖ * ‖V ((t : ℂ) * Complex.I) x‖ := by
    rw [← norm_mul, ← norm_mul, hkey]
  have hGpos : 0 < ‖G ((t : ℂ) * Complex.I)‖ := norm_pos_iff.mpr hG0
  have hle : ‖Eψ ((t : ℂ) * Complex.I) x -
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
        (fun u => unipotentGL2 u) (Eψ ((t : ℂ) * Complex.I)) x‖ * ‖G ((t : ℂ) * Complex.I)‖
      ≤ (C₁ * C₂ * D ^ (A₁ + A₂) * H ^ (-(N' : ℝ))) * ‖G ((t : ℂ) * Complex.I)‖ := by
    rw [hnorm]
    calc ‖p ((t : ℂ) * Complex.I)‖ * ‖V ((t : ℂ) * Complex.I) x‖
        ≤ (C₂ * D ^ A₂ * ‖G ((t : ℂ) * Complex.I)‖) * (C₁ * D ^ A₁ * H ^ (-(N' : ℝ))) :=
          mul_le_mul hpG hVn (norm_nonneg _) (by positivity)
      _ = (C₁ * C₂ * D ^ (A₁ + A₂) * H ^ (-(N' : ℝ))) * ‖G ((t : ℂ) * Complex.I)‖ := by rw [pow_add]; ring
  exact le_of_mul_le_mul_right hle hGpos

end S_AutomorphicForm_exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat (solution)
