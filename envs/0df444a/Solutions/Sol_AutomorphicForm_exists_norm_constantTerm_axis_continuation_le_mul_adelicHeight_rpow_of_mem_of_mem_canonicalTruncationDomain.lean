-- Prove2me | solution 1 for AutomorphicForm.exists_norm_constantTerm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_of_mem_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b442dea0-b6c6-56e5-bd3f-04176b520efc

import Theorems.Thm_AutomorphicForm_analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family
import Theorems.Thm_AutomorphicForm_exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection
import Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half
import Theorems.Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_norm_constantTerm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_of_mem_canonicalTruncationDomain
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (s : ℂ), s ∈ Oφ → ∃ (M A : ℝ), ∀ (g : AdelicGL2 (𝓞 F) F),
        g ∈ AutomorphicForm.canonicalTruncationDomain F α β →
        ‖@AutomorphicForm.constantTerm _ (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _ (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t) (Eφ s) g‖ ≤
          M * (NumberField.AdelicHeight.adelicHeight F g) ^ A := by
  intro αm hαm μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu Oφ Eφ Nφ hEφ s hs
  obtain ⟨hO, hOc, hax, hhalf, hEa, hNa, hEjc, hNjc, hE, hN⟩ := hEφ

  have hφc : ∀ z : ℂ, Continuous (φf z) := fun z =>
    hφfjc.comp (continuous_const.prodMk continuous_id)
  have hNc : Continuous (Nφ s) := by
    have h2 : Continuous (fun g : AdelicGL2 (𝓞 F) F => ((s, g) : ℂ × AdelicGL2 (𝓞 F) F)) :=
      continuous_const.prodMk continuous_id
    exact hNjc.comp_continuous h2 (fun g => ⟨hs, Set.mem_univ _⟩)

  have hE' : ∀ z : ℂ, 1 / 2 < z.re → ∀ g : AdelicGL2 (𝓞 F) F,
      Eφ z g = AutomorphicForm.pseudoEisenstein F (φf z) g := fun z hz g => by
    rw [hE z hz g, AutomorphicForm.pseudoEisenstein_apply]
  have hCT := (AutomorphicForm.analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family F hαm
    μ ν hμ hν hμF hνF φf hφf hφfK hφff hφfjc hφfhol hφfKu Oφ Eφ Nφ hO hOc hhalf hEa hNa hEjc hNjc
    hE' hN).2.2 s hs

  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    AutomorphicForm.exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection F hαm μ ν hμ hν s
      (φf s) (hφf s) (hφc s)

  have h1 : (1 : ℂ) ∈ Oφ := hhalf (by simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num)
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1mem : {z : ℂ | 1 / 2 < z.re} ∈ nhds (1 : ℂ) :=
    hopen.mem_nhds (by simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num)
  have hcpow : ∀ (x : (AdeleRing (𝓞 F) F)ˣ) (w : ℂ),
      AnalyticOnNhd ℂ (fun z : ℂ => ((cpowChar αm hαm (-z + w) x : ℂˣ) : ℂ)) Oφ := by
    intro x w
    have hx0 : ((((αm x : ℝˣ) : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (hαm x).ne'
    have hd : Differentiable ℂ (fun z : ℂ => ((((αm x : ℝˣ) : ℝ) : ℂ)) ^ (-z + w)) := fun z =>
      ((differentiableAt_id.neg).add_const w).const_cpow (Or.inl hx0)
    simpa only [cpowChar_apply_val] using hd.differentiableOn.analyticOnNhd hO
  have hNind : IsInducedSection (𝓞 F) F (etaFst ν αm hαm (-s)) (etaSnd μ αm hαm (-s)) (Nφ s) := by
    intro b hb g
    have hu : AnalyticOnNhd ℂ (fun z => Nφ z (b * g)) Oφ := hNa _
    have hv : AnalyticOnNhd ℂ (fun z =>
        ((etaFst ν αm hαm (-z) (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
        ((etaSnd μ αm hαm (-z) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
        Nφ z g) Oφ := by
      have hA : AnalyticOnNhd ℂ (fun z =>
          ((etaFst ν αm hαm (-z) (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)) Oφ := by
        have := (analyticOnNhd_const (v := ((ν (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ))).mul
          (hcpow (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) (1 / 2))
        simpa only [etaFst_apply, Units.val_mul] using this
      have hB : AnalyticOnNhd ℂ (fun z =>
          ((etaSnd μ αm hαm (-z) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)) Oφ := by
        have hx0 : ((((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) : ℂ)) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (hαm _).ne'
        have hd : Differentiable ℂ (fun z : ℂ =>
            ((((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) : ℂ)) ^ (-(-z + 1 / 2))) :=
          fun z => (((differentiableAt_id.neg).add_const (1 / 2 : ℂ)).neg).const_cpow (Or.inl hx0)
        have := (analyticOnNhd_const (v := ((μ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ))).mul
          (hd.differentiableOn.analyticOnNhd hO)
        simpa only [etaSnd_apply, Units.val_mul, cpowChar_apply_val] using this
      exact (hA.mul hB).mul (hNa g)
    have key : ∀ z : ℂ, 1 / 2 < z.re →
        Nφ z (b * g) =
          ((etaFst ν αm hαm (-z) (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
          ((etaSnd μ αm hαm (-z) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
          Nφ z g := by
      intro z hz
      have hI := (AutomorphicForm.isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half F
        hαm μ ν hμ hν z hz (φf z) (hφf z) (hφc z)).1
      rw [hN z hz (b * g), hN z hz g]
      exact hI b hb g
    have hfg : (fun z => Nφ z (b * g)) =ᶠ[nhds (1 : ℂ)] (fun z =>
        ((etaFst ν αm hαm (-z) (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
        ((etaSnd μ αm hαm (-z) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
        Nφ z g) := Filter.eventuallyEq_of_mem h1mem (fun z hz => key z hz)
    exact (hu.eqOn_of_preconnected_of_eventuallyEq hv hOc h1 hfg) hs
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    AutomorphicForm.exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection F hαm ν μ hν hμ (-s)
      (Nφ s) hNind hNc

  obtain ⟨h₀, hh₀, hfloor, -⟩ :=
    AutomorphicForm.exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
      F α β hα hαβ

  refine ⟨C₁ * h₀ ^ ((s.re + 1 / 2) - max (s.re + 1 / 2) ((-s).re + 1 / 2)) +
      ‖((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹‖ * C₂ *
        h₀ ^ (((-s).re + 1 / 2) - max (s.re + 1 / 2) ((-s).re + 1 / 2)),
    max (s.re + 1 / 2) ((-s).re + 1 / 2), ?_⟩
  intro g hg
  have hH : h₀ ≤ NumberField.AdelicHeight.adelicHeight F g := hfloor g hg
  have hHpos : 0 < NumberField.AdelicHeight.adelicHeight F g := hh₀.trans_le hH
  have hkey : ∀ a A : ℝ, a ≤ A →
      NumberField.AdelicHeight.adelicHeight F g ^ a ≤
        h₀ ^ (a - A) * NumberField.AdelicHeight.adelicHeight F g ^ A := by
    intro a A ha
    have hsplit : NumberField.AdelicHeight.adelicHeight F g ^ a =
        NumberField.AdelicHeight.adelicHeight F g ^ (a - A) * NumberField.AdelicHeight.adelicHeight F g ^ A := by
      rw [← Real.rpow_add hHpos]; congr 1; ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hh₀ hH (sub_nonpos.mpr ha))
      (Real.rpow_nonneg hHpos.le A)
  have hCTg : @AutomorphicForm.constantTerm _ (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _ (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
      (fun t => AutomorphicForm.unipotentGL2 t) (Eφ s) g =
      φf s g + ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ s g := hCT g
  rw [hCTg]
  have e1 := hkey (s.re + 1 / 2) (max (s.re + 1 / 2) ((-s).re + 1 / 2)) (le_max_left _ _)
  have e2 := hkey ((-s).re + 1 / 2) (max (s.re + 1 / 2) ((-s).re + 1 / 2)) (le_max_right _ _)
  calc ‖φf s g + ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ s g‖
      ≤ ‖φf s g‖ + ‖((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹‖ * ‖Nφ s g‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ C₁ * NumberField.AdelicHeight.adelicHeight F g ^ (s.re + 1 / 2) +
        ‖((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹‖ *
          (C₂ * NumberField.AdelicHeight.adelicHeight F g ^ ((-s).re + 1 / 2)) := by
        gcongr
        · exact hC₁ g
        · exact hC₂ g
    _ ≤ C₁ * (h₀ ^ ((s.re + 1 / 2) - max (s.re + 1 / 2) ((-s).re + 1 / 2)) *
            NumberField.AdelicHeight.adelicHeight F g ^ (max (s.re + 1 / 2) ((-s).re + 1 / 2))) +
        ‖((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹‖ *
          (C₂ * (h₀ ^ (((-s).re + 1 / 2) - max (s.re + 1 / 2) ((-s).re + 1 / 2)) *
            NumberField.AdelicHeight.adelicHeight F g ^ (max (s.re + 1 / 2) ((-s).re + 1 / 2)))) := by
        gcongr
    _ = _ := by ring

end S_AutomorphicForm_exists_norm_constantTerm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_of_mem_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_constantTerm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_of_mem_canonicalTruncationDomain (solution)
