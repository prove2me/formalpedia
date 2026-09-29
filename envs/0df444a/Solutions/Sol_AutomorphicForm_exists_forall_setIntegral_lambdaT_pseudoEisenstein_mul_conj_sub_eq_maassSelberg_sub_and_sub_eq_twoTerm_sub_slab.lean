-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8ef6b51f-19af-5fb2-8952-5f171b6cc88d

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
import Theorems.Thm_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
import Theorems.Thm_NumberField_TateGlobal_setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_peterssonIntegral_lambdaT_sub_eq_integral_constantTerm_mul_conj_constantTerm
import Theorems.Thm_AutomorphicForm_integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa
import Theorems.Thm_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
import Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable
import Theorems.Thm_AutomorphicForm_memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half
import Theorems.Thm_AutomorphicForm_continuous_pseudoEisenstein_of_isInducedSection_of_re_gt_half
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one"
p2m_attr_erase "simp" "AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal AutomorphicForm
open scoped NNReal ENNReal Topology ComplexConjugate

noncomputable section

namespace R1SlabINCBoth

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

theorem secondCountableTopology_units {M : Type*} [TopologicalSpace M] [Monoid M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountableTopology_ideles : SecondCountableTopology (𝔸)ˣ := by
  haveI : SecondCountableTopology 𝔸 := NumberField.AdeleRing.secondCountableTopology F
  exact secondCountableTopology_units

theorem measurable_ideleNorm : Measurable (ideleNorm F) :=
  (NumberField.TateGlobal.continuous_ideleNorm F).measurable

theorem principalIdeles_eq :
    M4aHerbrand.principalIdeles (𝓞 F) F
      = (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range := rfl

theorem continuous_diagOne : Continuous (NumberField.AdelicLevel.diagOne : (𝔸)ˣ → AdelicGL2 (𝓞 F) F) := by
  have hvec : ∀ (f : (𝔸)ˣ → 𝔸), Continuous f → Continuous fun a : (𝔸)ˣ => (![f a, 1] : Fin 2 → 𝔸) := by
    intro f hf
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact hf
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ a : (𝔸)ˣ, ((NumberField.AdelicLevel.diagOne a : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) 𝔸) = Matrix.diagonal ![(a : 𝔸), 1] := fun a => rfl
    have hc : Continuous fun a : (𝔸)ˣ => Matrix.diagonal ![(a : 𝔸), 1] :=
      (hvec _ Units.continuous_val).matrix_diagonal
    exact hc.congr fun a => (h a).symm
  · have h : ∀ a : (𝔸)ˣ, (((NumberField.AdelicLevel.diagOne a : AdelicGL2 (𝓞 F) F)⁻¹ : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) 𝔸) = Matrix.diagonal ![((a⁻¹ : (𝔸)ˣ) : 𝔸), 1] := by
      intro a; rw [← map_inv]; rfl
    have hc : Continuous fun a : (𝔸)ˣ => Matrix.diagonal ![((a⁻¹ : (𝔸)ˣ) : 𝔸), 1] :=
      (hvec _ (Units.continuous_val.comp continuous_inv)).matrix_diagonal
    exact hc.congr fun a => (h a).symm

theorem discreteTopology_of_le_range (B : Subgroup (AdelicGL2 (𝓞 F) F))
    (hB : B ≤ (globalPoints (𝓞 F) F).range) : DiscreteTopology B := by
  set gp := globalPoints (𝓞 F) F with hgp
  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 F) F)
  have hfin : {γ : GL (Fin 2) F | (1 : AdelicGL2 (𝓞 F) F)⁻¹ * gp γ * 1 ∈ C}.Finite :=
    AutomorphicForm.adelicKernelLocalFiniteness F C hCc 1 1
  set R : Set (AdelicGL2 (𝓞 F) F) := gp '' {γ | gp γ ∈ C ∧ gp γ ≠ 1} with hR
  have hRfin : R.Finite := by
    refine (hfin.subset ?_).image gp
    intro γ hγ
    simpa using hγ.1
  set U : Set (AdelicGL2 (𝓞 F) F) := interior C \ R with hU
  have hUo : IsOpen U := isOpen_interior.sdiff hRfin.isClosed
  have h1U : (1 : AdelicGL2 (𝓞 F) F) ∈ U := by
    refine ⟨mem_interior_iff_mem_nhds.2 hC1, ?_⟩
    rintro ⟨γ, ⟨-, hne⟩, h1⟩; exact hne h1
  have hkey : ∀ x ∈ gp.range, x ∈ U → x = 1 := by
    rintro _ ⟨γ, rfl⟩ ⟨hint, hnot⟩
    by_contra hne
    exact hnot ⟨γ, ⟨interior_subset hint, hne⟩, rfl⟩
  apply discreteTopology_of_isOpen_singleton_one
  have hset : ({1} : Set B) = ((↑) : B → AdelicGL2 (𝓞 F) F) ⁻¹' U := by
    ext b
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl; exact h1U
    · intro hb
      exact Subtype.ext (hkey b (hB b.2) hb)
  rw [hset]
  exact hUo.preimage continuous_subtype_val

theorem discreteTopology_principalIdeles :
    DiscreteTopology (M4aHerbrand.principalIdeles (𝓞 F) F) := by
  set P := M4aHerbrand.principalIdeles (𝓞 F) F with hP
  set ι : (𝔸)ˣ →* AdelicGL2 (𝓞 F) F := NumberField.AdelicLevel.diagOne with hι
  set Γ : Subgroup (AdelicGL2 (𝓞 F) F) := (globalPoints (𝓞 F) F).range with hΓ
  haveI hΓd : DiscreteTopology Γ := discreteTopology_of_le_range F Γ le_rfl

  have hmap : ∀ p : P, ι (p : (𝔸)ˣ) ∈ Γ := by
    rintro ⟨_, u, rfl⟩
    refine ⟨NumberField.AdelicLevel.diagOne u, ?_⟩
    apply Units.ext
    ext i j
    show algebraMap F 𝔸 ((NumberField.AdelicLevel.diagOne u : Matrix (Fin 2) (Fin 2) F) i j)
      = (NumberField.AdelicLevel.diagOne (Units.map (algebraMap F 𝔸 : F →* 𝔸) u) :
          Matrix (Fin 2) (Fin 2) 𝔸) i j
    rw [NumberField.AdelicLevel.diagOne_coe_apply, NumberField.AdelicLevel.diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  set f : P → Γ := fun p => ⟨ι (p : (𝔸)ˣ), hmap p⟩ with hf
  have hfc : Continuous f :=
    ((continuous_diagOne F).comp continuous_subtype_val).subtype_mk _
  have hfinj : ∀ p : P, f p = f 1 → p = 1 := by
    intro p h
    have h' : ι (p : (𝔸)ˣ) = ι 1 := by
      have := congrArg (fun x : Γ => (x : AdelicGL2 (𝓞 F) F)) h
      simpa [hf] using this
    have h00 := congrArg (fun m : AdelicGL2 (𝓞 F) F => (m : Matrix (Fin 2) (Fin 2) 𝔸) 0 0) h'
    simp only [hι, NumberField.AdelicLevel.diagOne_coe_apply, map_one] at h00
    have hp : ((p : (𝔸)ˣ) : 𝔸) = 1 := by simpa [Matrix.diagonal] using h00
    exact Subtype.ext (Units.ext hp)
  apply discreteTopology_of_isOpen_singleton_one
  have hset : ({1} : Set P) = f ⁻¹' {f 1} := by
    ext p
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => by rw [h], fun h => hfinj p h⟩
  rw [hset]
  exact (isOpen_discrete _).preimage hfc

theorem exists_fundamentalDomain_principalIdeles :
    ∃ D : Set (𝔸)ˣ, MeasurableSet D ∧
      ∀ μ : Measure (𝔸)ˣ, IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D μ := by
  haveI := secondCountableTopology_ideles F
  obtain ⟨D, hDm, huniq, -⟩ :=
    MeasureTheory.exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
      (M4aHerbrand.principalIdeles (𝓞 F) F) (discreteTopology_principalIdeles F)
  refine ⟨D, hDm, fun μ => IsFundamentalDomain.mk' hDm.nullMeasurableSet fun x => ?_⟩
  obtain ⟨γ, hγ, hγu⟩ := huniq x
  refine ⟨γ, ?_, fun γ' hγ' => hγu γ' ?_⟩
  · show ((γ : (𝔸)ˣ) * x) ∈ D
    rwa [mul_comm]
  · have : ((γ' : (𝔸)ˣ) * x) ∈ D := hγ'
    rwa [mul_comm] at this

variable {F}

theorem conj_unitary {χ : (𝔸)ˣ →* ℂˣ} (hχ : IsUnitaryChar (𝓞 F) F χ) (x : (𝔸)ˣ) :
    conj ((χ x : ℂˣ) : ℂ) = ((χ x : ℂˣ) : ℂ)⁻¹ :=
  (Complex.inv_eq_conj (hχ x)).symm

theorem conj_ofReal_cpow {r : ℝ} (hr : 0 ≤ r) (w : ℂ) :
    conj (((r : ℝ) : ℂ) ^ w) = ((r : ℝ) : ℂ) ^ (conj w) := by
  have harg : ((r : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr]; exact Real.pi_pos.ne
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

theorem conj_half : conj ((1 / 2 : ℂ)) = 1 / 2 := by
  rw [map_div₀, map_one, map_ofNat]

theorem conj_etaFst_val {μ : (𝔸)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ)
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (𝔸)ˣ) :
    conj ((etaFst μ α hα s x : ℂˣ) : ℂ)
      = ((μ x : ℂˣ) : ℂ)⁻¹ * (((α x : ℝˣ) : ℝ) : ℂ) ^ (conj s + 1 / 2) := by
  rw [etaFst_apply, Units.val_mul, map_mul, conj_unitary hμ, cpowChar_apply_val,
    conj_ofReal_cpow (hα x).le, map_add, conj_half]

theorem conj_etaSnd_val {ν : (𝔸)ˣ →* ℂˣ} (hν : IsUnitaryChar (𝓞 F) F ν)
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (𝔸)ˣ) :
    conj ((etaSnd ν α hα s x : ℂˣ) : ℂ)
      = ((ν x : ℂˣ) : ℂ)⁻¹ * (((α x : ℝˣ) : ℝ) : ℂ) ^ (-(conj s + 1 / 2)) := by
  rw [etaSnd_apply, Units.val_mul, map_mul, conj_unitary hν, cpowChar_apply_val,
    conj_ofReal_cpow (hα x).le, map_neg, map_add, conj_half]

theorem integrand_eq {μ ν μ' ν' : (𝔸)ˣ →* ℂˣ}
    (hμ' : IsUnitaryChar (𝓞 F) F μ') (hν' : IsUnitaryChar (𝓞 F) F ν')
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s s' : ℂ) (z t : (𝔸)ˣ) (A B : ℂ) :
    ((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ)
        * conj (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' z : ℂˣ) : ℂ))
        * A * B * ((((α t : ℝˣ) : ℝ)⁻¹ : ℝ) : ℂ)
      = (((μ t : ℂˣ) : ℂ) * ((μ' t : ℂˣ) : ℂ)⁻¹)
        * ((((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * ((μ' z : ℂˣ) : ℂ)⁻¹ * ((ν' z : ℂˣ) : ℂ)⁻¹)
          * (((α t : ℝˣ) : ℝ) : ℂ) ^ (s + conj s') * A * B) := by
  have hz : (((α z : ℝˣ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα z).ne'
  have ht : (((α t : ℝˣ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα t).ne'
  rw [map_mul (starRingEnd ℂ), conj_etaFst_val hμ', conj_etaSnd_val hν', etaFst_apply, etaSnd_apply]
  simp only [Units.val_mul, cpowChar_apply_val, map_mul, Complex.ofReal_mul, Complex.ofReal_inv, mul_inv,
    Complex.mul_cpow_ofReal_nonneg (hα z).le (hα t).le]

  have hzpow : (((α z : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) * (((α z : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2))
      * ((((α z : ℝˣ) : ℝ) : ℂ) ^ (conj s' + 1 / 2) * (((α z : ℝˣ) : ℝ) : ℂ) ^ (-(conj s' + 1 / 2))) = 1 := by
    rw [← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz, add_neg_cancel, add_neg_cancel,
      Complex.cpow_zero, mul_one]
  have htpow : (((α t : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) * (((α t : ℝˣ) : ℝ) : ℂ) ^ (conj s' + 1 / 2)
      * ((((α t : ℝˣ) : ℝ) : ℂ))⁻¹ = (((α t : ℝˣ) : ℝ) : ℂ) ^ (s + conj s') := by
    rw [← Complex.cpow_add _ _ ht, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ ht]
    congr 1; ring
  rw [← htpow]
  linear_combination
    (((μ z : ℂˣ) : ℂ) * ((μ t : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * ((μ' z : ℂˣ) : ℂ)⁻¹ * ((μ' t : ℂˣ) : ℂ)⁻¹
      * ((ν' z : ℂˣ) : ℂ)⁻¹ * A * B
      * ((((α t : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) * (((α t : ℝˣ) : ℝ) : ℂ) ^ (conj s' + 1 / 2)
        * ((((α t : ℝˣ) : ℝ) : ℂ))⁻¹)) * hzpow

variable (F)

def radial (R R' : ℝ) (W : ℂ) : ℝ → ℂ := fun r =>
  (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) r * ((r : ℝ) : ℂ) ^ W

theorem measurable_radial (R R' : ℝ) (W : ℂ) : Measurable (radial R R' W) := by
  unfold radial
  refine Measurable.mul (measurable_const.indicator measurableSet_Ioc) ?_
  exact (Complex.measurable_ofReal).pow_const W

theorem norm_radial_le (R R' : ℝ) (W : ℂ) (r : ℝ) :
    ‖radial R R' W r‖ ≤ (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℝ)) r
      * max (Real.exp R ^ W.re) (Real.exp R' ^ W.re) := by
  unfold radial
  by_cases hr : r ∈ Set.Ioc (Real.exp R) (Real.exp R')
  · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, one_mul, one_mul]
    have hr0 : 0 < r := (Real.exp_pos R).trans hr.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr0]
    rcases le_total 0 W.re with hW | hW
    · exact le_max_of_le_right (Real.rpow_le_rpow hr0.le hr.2 hW)
    · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos (Real.exp_pos R) hr.1.le hW)
  · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, zero_mul, zero_mul, norm_zero]

theorem integral_radial (R R' : ℝ) (hRR' : R ≤ R') (W : ℂ) (hW : W ≠ 0) :
    ∫ r in Set.Ioi (0 : ℝ), ((r : ℝ) : ℂ)⁻¹ * radial R R' W r
      = (Complex.exp ((R' : ℂ) * W) - Complex.exp ((R : ℂ) * W)) / W := by
  have hexp : Real.exp R ≤ Real.exp R' := Real.exp_le_exp.2 hRR'
  have hsub : Set.Ioc (Real.exp R) (Real.exp R') ⊆ Set.Ioi 0 := fun r hr => (Real.exp_pos R).trans hr.1
  have hind : (fun r : ℝ => ((r : ℝ) : ℂ)⁻¹ * radial R R' W r)
      = (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun r => ((r : ℝ) : ℂ) ^ (W - 1)) := by
    funext r
    unfold radial
    by_cases hr : r ∈ Set.Ioc (Real.exp R) (Real.exp R')
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, one_mul]
      have hr0 : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ((Real.exp_pos R).trans hr.1).ne'
      rw [Complex.cpow_sub _ _ hr0, Complex.cpow_one, div_eq_mul_inv, mul_comm]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]; simp
  rw [hind, setIntegral_indicator measurableSet_Ioc, Set.inter_eq_self_of_subset_right hsub,
    ← intervalIntegral.integral_of_le hexp, integral_cpow]
  · rw [sub_add_cancel]
    have h1 : ((Real.exp R' : ℝ) : ℂ) ^ W = Complex.exp ((R' : ℂ) * W) := by
      rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
        Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_pos.le)]
    have h2 : ((Real.exp R : ℝ) : ℂ) ^ W = Complex.exp ((R : ℂ) * W) := by
      rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
        Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_pos.le)]
    rw [h1, h2]
  · right
    refine ⟨by simpa using hW, ?_⟩
    rw [Set.uIcc_of_le hexp]
    exact fun h => (lt_irrefl (0 : ℝ)) ((Real.exp_pos R).trans_le h.1)

theorem integrableOn_radial (R R' : ℝ) (W : ℂ) :
    IntegrableOn (fun r : ℝ => ((r : ℝ) : ℂ)⁻¹ * radial R R' W r) (Set.Ioi 0) := by
  have hind : (fun r : ℝ => ((r : ℝ) : ℂ)⁻¹ * radial R R' W r)
      = (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun r => ((r : ℝ) : ℂ)⁻¹ * ((r : ℝ) : ℂ) ^ W) := by
    funext r
    unfold radial
    by_cases hr : r ∈ Set.Ioc (Real.exp R) (Real.exp R')
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, one_mul]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, zero_mul, mul_zero]
  rw [hind]
  refine Integrable.integrableOn ((integrable_indicator_iff measurableSet_Ioc).2 ?_)
  have hcont : ContinuousOn (fun r : ℝ => ((r : ℝ) : ℂ)⁻¹ * ((r : ℝ) : ℂ) ^ W)
      (Set.Icc (Real.exp R) (Real.exp R')) := by
    intro r hr
    have hr0 : 0 < r := (Real.exp_pos R).trans_le hr.1
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul ?_ ?_
    · exact (Complex.continuous_ofReal.continuousAt).inv₀ (Complex.ofReal_ne_zero.mpr hr0.ne')
    · exact (Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
        (Or.inl (by simpa using hr0))
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

theorem band_integral
    (D D' : Set (𝔸)ˣ) (a b : ℝ)
    (Cs : ℝ≥0∞) (hCs_top : Cs ≠ ∞)
    (hCs : ∀ r : ℝ, 0 < r →
      (NumberField.Idele.idelicHaar F) (D ∩ {z | ideleNorm F z ^ 2 * r ∈ Set.Icc a b}) = Cs)
    (Cn : ℝ)
    (hCn : ∀ g : ℝ → ℂ, Measurable g →
      (IntegrableOn (fun x => g (ideleNorm F x)) D' (NumberField.Idele.idelicHaar F) ↔
          IntegrableOn (fun r : ℝ => (r : ℂ)⁻¹ * g r) (Set.Ioi (0 : ℝ))) ∧
        ∫ x in D', g (ideleNorm F x) ∂(NumberField.Idele.idelicHaar F) =
          Cn * ∫ r in Set.Ioi (0 : ℝ), (r : ℂ)⁻¹ * g r)
    (W : ℂ) (hW : W ≠ 0) (R R' : ℝ) (hRR' : R ≤ R') :
    ∫ z in D, ∫ t in D',
        (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t)
          * ((Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t)
            * ((ideleNorm F t : ℝ) : ℂ) ^ W)
      ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
      = (Cs.toReal : ℂ) * Cn * ((Complex.exp ((R' : ℂ) * W) - Complex.exp ((R : ℂ) * W)) / W) := by
  set ν := NumberField.Idele.idelicHaar F with hν
  set G : (𝔸)ˣ → ℂ := fun t => radial R R' W (ideleNorm F t) with hG
  set S : (𝔸)ˣ → Set (𝔸)ˣ := fun t => {z | ideleNorm F z ^ 2 * ideleNorm F t ∈ Set.Icc a b} with hS
  have hSm : ∀ t, MeasurableSet (S t) := fun t =>
    (((measurable_ideleNorm F).pow_const 2).mul_const _) measurableSet_Icc
  have hind : ∀ z t, (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t)
      = (S t).indicator (fun _ => (1 : ℂ)) z := by
    intro z t
    by_cases h : ideleNorm F z ^ 2 * ideleNorm F t ∈ Set.Icc a b
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show z ∈ S t from h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show z ∉ S t from h)]
  have hGm : Measurable G := (measurable_radial R R' W).comp (measurable_ideleNorm F)

  set Φ : (𝔸)ˣ → (𝔸)ˣ → ℂ := fun z t => (S t).indicator (fun _ => (1 : ℂ)) z * G t with hΦ
  have hΦeq : ∀ z t, (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t)
      * ((Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t)
        * ((ideleNorm F t : ℝ) : ℂ) ^ W) = Φ z t := by
    intro z t; simp only [hΦ, hG, radial, hind]
  simp_rw [hΦeq]

  have hGint : IntegrableOn G D' ν := by
    have := (hCn (radial R R' W) (measurable_radial R R' W)).1
    exact this.2 (integrableOn_radial R R' W)

  have hνS : ∀ t, ν (D ∩ S t) = Cs := fun t => hCs (ideleNorm F t) (ideleNorm_pos t)
  have hνS' : ∀ t, (ν.restrict D) (S t) = Cs := fun t => by
    rw [Measure.restrict_apply (hSm t), Set.inter_comm, hνS]

  have hinner : ∀ t, ∫ z in D, Φ z t ∂ν = (Cs.toReal : ℂ) * G t := by
    intro t
    simp only [hΦ]
    rw [integral_mul_const, integral_indicator_const _ (hSm t), measureReal_def, hνS',
      Complex.real_smul, mul_one]
  have hinner_norm : ∀ t, ∫ z in D, ‖Φ z t‖ ∂ν = Cs.toReal * ‖G t‖ := by
    intro t
    have : (fun z => ‖Φ z t‖) = fun z => (S t).indicator (fun _ => ‖G t‖) z := by
      funext z
      simp only [hΦ]
      by_cases hz : z ∈ S t
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul, norm_zero]
    rw [this, integral_indicator_const _ (hSm t), measureReal_def, hνS', smul_eq_mul]

  haveI : SecondCountableTopology (𝔸)ˣ := secondCountableTopology_ideles F
  haveI : SigmaFinite ν := by rw [hν]; infer_instance
  have hmeasΦ : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable fun p : (𝔸)ˣ × (𝔸)ˣ => ideleNorm F p.1 ^ 2 * ideleNorm F p.2 :=
      (((measurable_ideleNorm F).comp measurable_fst).pow_const 2).mul
        ((measurable_ideleNorm F).comp measurable_snd)
    have h2 : Measurable fun p : (𝔸)ˣ × (𝔸)ˣ =>
        (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F p.1 ^ 2 * ideleNorm F p.2) :=
      (measurable_const.indicator measurableSet_Icc).comp h1
    have h3 : Measurable fun p : (𝔸)ˣ × (𝔸)ˣ => G p.2 := hGm.comp measurable_snd
    have : Function.uncurry Φ = fun p : (𝔸)ˣ × (𝔸)ˣ =>
        (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F p.1 ^ 2 * ideleNorm F p.2) * G p.2 := by
      funext p; simp only [Function.uncurry, hΦ, hind]
    rw [this]
    exact h2.mul h3
  have hint : Integrable (Function.uncurry Φ) ((ν.restrict D).prod (ν.restrict D')) := by
    refine (integrable_prod_iff' hmeasΦ.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall fun t => ?_
      show Integrable (fun z => (S t).indicator (fun _ => (1 : ℂ)) z * G t) (ν.restrict D)
      have : (fun z => (S t).indicator (fun _ => (1 : ℂ)) z * G t)
          = (S t).indicator (fun _ => G t) := by
        funext z
        by_cases hz : z ∈ S t
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
      rw [this, integrable_indicator_iff (hSm t)]
      refine integrableOn_const ?_
      rw [hνS']; exact hCs_top
    · have : (fun t => ∫ z, ‖Function.uncurry Φ (z, t)‖ ∂(ν.restrict D)) = fun t => Cs.toReal * ‖G t‖ := by
        funext t; exact hinner_norm t
      rw [this]
      exact (hGint.norm.const_mul _)

  have hswap : ∫ z in D, ∫ t in D', Φ z t ∂ν ∂ν = ∫ t in D', ∫ z in D, Φ z t ∂ν ∂ν :=
    integral_integral_swap hint
  rw [hswap]
  simp_rw [hinner]
  rw [integral_const_mul]

  have ht : ∫ t in D', G t ∂ν = Cn * ∫ r in Set.Ioi (0 : ℝ), ((r : ℝ) : ℂ)⁻¹ * radial R R' W r :=
    (hCn (radial R R' W) (measurable_radial R R' W)).2
  rw [ht, integral_radial R R' hRR' W hW]
  ring

theorem twisted_band_integral_eq_zero
    (D D' : Set (𝔸)ˣ)
    (hD'F : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
    (χ : (𝔸)ˣ →* ℂˣ) (hχF : IsIdeleClassChar (𝓞 F) F χ)
    (hχ : ∃ z : (𝔸)ˣ, ideleNorm F z = 1 ∧ χ z ≠ 1)
    (h : (𝔸)ˣ → ℝ → ℂ) :
    ∫ z in D, ∫ t in D', ((χ t : ℂˣ) : ℂ) * h z (ideleNorm F t)
      ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) = 0 := by
  have hz : ∀ z, ∫ t in D', ((χ t : ℂˣ) : ℂ) * h z (ideleNorm F t) ∂(NumberField.Idele.idelicHaar F) = 0 :=
    fun z =>
      NumberField.TateGlobal.setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
        F (NumberField.Idele.idelicHaar F) D' hD'F χ hχF hχ (h z)
  simp_rw [hz]
  exact integral_zero _ _

end R1SlabINCBoth

end

noncomputable section

namespace R1SlabINCBoth

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

open NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

theorem peterssonIntegral_zero (S : Set (AdelicGL2 (𝓞 F) F)) (x y : AdelicGL2 (𝓞 F) F → ℂ) :
    peterssonIntegral F 0 S x y = ∫ g in S, x g * conj (y g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  unfold peterssonIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]

variable {F}

theorem memLp_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} {p : ℝ≥0∞}
    (hf : MemLp f p μ) : MemLp (fun x => conj (f x)) p μ := by
  refine hf.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hf.1) ?_
  exact Filter.Eventually.of_forall fun x => by simp

theorem isPrincipalTrivial_alpha :
    IsPrincipalTrivial (R := 𝓞 F) (K := F)
      (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits) := by
  intro u
  apply Units.ext
  show ((distribHaarChar (AdeleRing (𝓞 F) F) (Units.map (algebraMap F 𝔸 : F →* 𝔸) u) : ℝ≥0) : ℝ) = 1
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
  have : Units.map (algebraMap F 𝔸).toMonoidHom u = Units.map (algebraMap F 𝔸 : F →* 𝔸) u := rfl
  rw [this] at h
  rw [h]; rfl

theorem section_borel_invariant
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α)
    {μ ν : (𝔸)ˣ →* ℂˣ} (hμF : IsIdeleClassChar (𝓞 F) F μ) (hνF : IsIdeleClassChar (𝓞 F) F ν)
    (s : ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) :
    ∀ b ∈ borelSubgroup F, ∀ y : AdelicGL2 (𝓞 F) F, φ (globalPoints (𝓞 F) F b * y) = φ y := by
  intro b hb y
  have hmem := globalPoints_mem_adelicBorel (𝓞 F) F hb
  rw [hφ (globalPoints (𝓞 F) F b) hmem y, borelDiagFst_globalPoints (𝓞 F) F hb hmem,
    borelDiagSnd_globalPoints (𝓞 F) F hb hmem, etaFst_isIdeleClassChar hμF hprin s,
    etaSnd_isIdeleClassChar hνF hprin s]
  simp

variable (F)

theorem main (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (s s' : ℂ) (_hs : 1 / 2 < s.re) (_hs' : 1 / 2 < s'.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ) (_hφK : AutomorphicForm.IsArchKFinite F φ) (_hφf : AutomorphicForm.IsKfSmooth F φ)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s') (AutomorphicForm.etaSnd ν αm hαm s') ψ)
      (_hψc : Continuous ψ) (_hψK : AutomorphicForm.IsArchKFinite F ψ) (_hψf : AutomorphicForm.IsKfSmooth F ψ),
    ∀ R R' : ℝ, R₀ ≤ R → R ≤ R' →
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => AutomorphicForm.unipotentGL2 t) (adelicHeight F) (Real.exp R) (pseudoEisenstein F φ) x *
          conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => AutomorphicForm.unipotentGL2 t) (adelicHeight F) (Real.exp R) (pseudoEisenstein F ψ) x))
        (canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => AutomorphicForm.unipotentGL2 t) (adelicHeight F) (Real.exp R') (pseudoEisenstein F φ) x *
          conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => AutomorphicForm.unipotentGL2 t) (adelicHeight F) (Real.exp R') (pseudoEisenstein F ψ) x))
        (canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      (μ = ν → s ≠ conj s' →
      ((∫ x in canonicalTruncationDomain F α β,
          AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => AutomorphicForm.unipotentGL2 t) (adelicHeight F) (Real.exp R') (pseudoEisenstein F φ) x *
          conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => AutomorphicForm.unipotentGL2 t) (adelicHeight F) (Real.exp R') (pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) -
       (∫ x in canonicalTruncationDomain F α β,
          AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => AutomorphicForm.unipotentGL2 t) (adelicHeight F) (Real.exp R) (pseudoEisenstein F φ) x *
          conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => AutomorphicForm.unipotentGL2 t) (adelicHeight F) (Real.exp R) (pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F))) =
      (c : ℂ) *
        (( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s + conj s'))) / (s + conj s')
          + (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s - conj s'))) / (s - conj s') ) -
         ( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s + conj s'))) / (s + conj s')
          + (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s - conj s'))) / (s - conj s') ))) ∧
      ((∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) →
      ((∫ x in canonicalTruncationDomain F α β,
          AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => AutomorphicForm.unipotentGL2 t) (adelicHeight F) (Real.exp R') (pseudoEisenstein F φ) x *
          conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => AutomorphicForm.unipotentGL2 t) (adelicHeight F) (Real.exp R') (pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) -
       (∫ x in canonicalTruncationDomain F α β,
          AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => AutomorphicForm.unipotentGL2 t) (adelicHeight F) (Real.exp R) (pseudoEisenstein F φ) x *
          conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => AutomorphicForm.unipotentGL2 t) (adelicHeight F) (Real.exp R) (pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F))) =
      (c : ℂ) *
        (( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s + conj s'))) / (s + conj s') ) -
         ( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s + conj s'))) / (s + conj s') ))) := by
  intro αm hαm

  set Haar : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hHaar
  set νb : Measure 𝔸 := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F) with hνb
  set H : AdelicGL2 (𝓞 F) F → ℝ := adelicHeight F with hH
  set Φ₀ : Set (AdelicGL2 (𝓞 F) F) := canonicalTruncationDomain F α β with hΦ₀
  set Λ : ℝ → (AdelicGL2 (𝓞 F) F → ℂ) → AdelicGL2 (𝓞 F) F → ℂ := fun R f =>
    AutomorphicForm.lambdaT νb (fun t => AutomorphicForm.unipotentGL2 t) H (Real.exp R) f with hΛ
  set vC : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)) with hvC
  set νI : Measure (𝔸)ˣ := NumberField.Idele.idelicHaar F with hνI
  set X0 : Set (AdelicGL2 (𝓞 F) F) :=
    {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hX0
  have hαI : ∀ t : (𝔸)ˣ, ((αm t : ℝˣ) : ℝ) = ideleNorm F t := fun t => rfl
  have hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) αm := isPrincipalTrivial_alpha

  obtain ⟨hc0, hTc, hΦS, hΦslab, hΦfd⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum F α β hα hαβ
  obtain ⟨R₁, hR₁⟩ :=
    AutomorphicForm.peterssonIntegral_lambdaT_sub_eq_integral_constantTerm_mul_conj_constantTerm F α β hα
      (canonicalTruncationFloor F α β) (canonicalTruncationWindow F α β) (canonicalTruncationLowerCut F α β)
      (canonicalTruncationUpperCut F α β) hc0 (canonicalTruncationTranslates F α β) hTc Φ₀ hΦS hΦslab hΦfd

  obtain ⟨cT, hcT0, hcTtop, hcT⟩ :=
    AutomorphicForm.exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa F
  obtain ⟨D, hDm, hDfd⟩ := exists_fundamentalDomain_principalIdeles F
  have hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D νI := hDfd νI
  have hDF' : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range D νI := hDF
  obtain ⟨Cs, hCs0, hCstop, hCs⟩ :=
    NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const F D hDm hDF α β hα hαβ
  obtain ⟨Cn, hCn0, hCn⟩ :=
    NumberField.TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
      F νI
  have hCnD := (hCn D hDF').1
  have hcTpos : 0 < cT.toReal := ENNReal.toReal_pos hcT0 hcTtop
  have hCspos : 0 < Cs.toReal := ENNReal.toReal_pos hCs0 hCstop
  refine ⟨cT.toReal * Cs.toReal * Cn, by positivity, R₁, ?_⟩
  intro μ ν hμ hν hμF hνF s s' hs hs' φ hφ hφc hφK hφf ψ hψ hψc hψK hψf R R' hR hRR'

  set E : AdelicGL2 (𝓞 F) F → ℂ := pseudoEisenstein F φ with hE
  set E' : AdelicGL2 (𝓞 F) F → ℂ := pseudoEisenstein F ψ with hE'
  have hEc : Continuous E :=
    AutomorphicForm.continuous_pseudoEisenstein_of_isInducedSection_of_re_gt_half F hαm μ ν hμ hν s hs φ hφ hφc
  have hE'c : Continuous E' :=
    AutomorphicForm.continuous_pseudoEisenstein_of_isInducedSection_of_re_gt_half F hαm μ ν hμ hν s' hs' ψ hψ hψc
  have hφB := section_borel_invariant αm hαm hprin hμF hνF s hφ
  have hψB := section_borel_invariant αm hαm hprin hμF hνF s' hψ
  have hEG : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), E (globalPoints (𝓞 F) F γ * g) = E g := by
    intro γ g
    have hsum := (AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hαm μ ν hμ hν s hs φ
      hφ hφc g).of_norm
    exact (AutomorphicForm.pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable F φ hφB g
      hsum γ).2
  have hE'G : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), E' (globalPoints (𝓞 F) F γ * g) = E' g := by
    intro γ g
    have hsum := (AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hαm μ ν hμ hν s' hs' ψ
      hψ hψc g).of_norm
    exact (AutomorphicForm.pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable F ψ hψB g
      hsum γ).2
  have hL2 : ∀ T : ℝ, MemLp (Λ T E) 2 (Haar.restrict Φ₀) := fun T =>
    AutomorphicForm.memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain F α β hα hαβ ∅ hαm μ ν
      hμ hν s hs φ hφ hφc hφK hφf T
  have hL2' : ∀ T : ℝ, MemLp (Λ T E') 2 (Haar.restrict Φ₀) := fun T =>
    AutomorphicForm.memLp_two_lambdaT_pseudoEisenstein_restrict_canonicalTruncationDomain F α β hα hαβ ∅ hαm μ ν
      hμ hν s' hs' ψ hψ hψc hψK hψf T
  have hprod : ∀ T : ℝ, IntegrableOn (fun x => Λ T E x * conj (Λ T E' x)) Φ₀ Haar := fun T =>
    (hL2 T).integrable_mul (memLp_conj (hL2' T))
  have hsq : IntegrableOn (fun g => ‖Λ R₁ E g‖ ^ 2) Φ₀ Haar :=
    (memLp_two_iff_integrable_sq_norm (hL2 R₁).1).1 (hL2 R₁)
  have hsq' : IntegrableOn (fun g => ‖Λ R₁ E' g‖ ^ 2) Φ₀ Haar :=
    (memLp_two_iff_integrable_sq_norm (hL2' R₁).1).1 (hL2' R₁)
  refine ⟨hprod R, hprod R', ?_⟩

  have hinc := hR₁ E E' hEc hE'c hEG hE'G hsq hsq' R R' hR hRR'
  rw [peterssonIntegral_zero, peterssonIntegral_zero] at hinc

  set φ₂ : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    vC⁻¹ * AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g with hφ₂
  set ψ₂ : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    vC⁻¹ * AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g with hψ₂
  have hCTφ : ∀ g, AutomorphicForm.constantTerm νb (fun t => AutomorphicForm.unipotentGL2 t) E g = φ g + φ₂ g :=
    fun g => AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F hαm μ ν hμ hν
      s hs φ hφ hφc g
  have hCTψ : ∀ g, AutomorphicForm.constantTerm νb (fun t => AutomorphicForm.unipotentGL2 t) E' g = ψ g + ψ₂ g :=
    fun g => AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F hαm μ ν hμ hν
      s' hs' ψ hψ hψc g

  obtain ⟨hMφI, hMφc⟩ := AutomorphicForm.isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half F
    hαm μ ν hμ hν s hs φ hφ hφc
  obtain ⟨hMψI, hMψc⟩ := AutomorphicForm.isInducedSection_and_continuous_weylIntertwiningIntegral_of_re_gt_half F
    hαm μ ν hμ hν s' hs' ψ hψ hψc
  have hφ₂I : IsInducedSection (𝓞 F) F (etaFst ν αm hαm (-s)) (etaSnd μ αm hαm (-s)) φ₂ :=
    (inducedSectionSubmodule (etaFst ν αm hαm (-s)) (etaSnd μ αm hαm (-s))).smul_mem vC⁻¹ hMφI
  have hψ₂I : IsInducedSection (𝓞 F) F (etaFst ν αm hαm (-s')) (etaSnd μ αm hαm (-s')) ψ₂ :=
    (inducedSectionSubmodule (etaFst ν αm hαm (-s')) (etaSnd μ αm hαm (-s'))).smul_mem vC⁻¹ hMψI
  have hφ₂c : Continuous φ₂ := continuous_const.mul hMφc
  have hψ₂c : Continuous ψ₂ := continuous_const.mul hMψc

  have h11 := AutomorphicForm.integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa F
    hαm cT hcTtop hcT D D hDm hDm hDF hDF μ ν μ ν hμ hν hμ hν hμF hνF hμF hνF s s' φ ψ hφ hψ hφc hψc α β R R' hα
  have h12 := AutomorphicForm.integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa F
    hαm cT hcTtop hcT D D hDm hDm hDF hDF μ ν ν μ hμ hν hν hμ hμF hνF hνF hμF s (-s') φ ψ₂ hφ hψ₂I hφc hψ₂c α β R R'
    hα
  have h21 := AutomorphicForm.integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa F
    hαm cT hcTtop hcT D D hDm hDm hDF hDF ν μ μ ν hν hμ hμ hν hνF hμF hμF hνF (-s) s' φ₂ ψ hφ₂I hψ hφ₂c hψc α β R R'
    hα
  have h22 := AutomorphicForm.integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa F
    hαm cT hcTtop hcT D D hDm hDm hDF hDF ν μ ν μ hν hμ hν hμ hνF hμF hνF hμF (-s) (-s') φ₂ ψ₂ hφ₂I hψ₂I hφ₂c hψ₂c
    α β R R' hα
  obtain ⟨hi11, hv11⟩ := h11
  obtain ⟨hi12, hv12⟩ := h12
  obtain ⟨hi21, hv21⟩ := h21
  obtain ⟨hi22, hv22⟩ := h22

  set m : Measure (RationalTorusUnipotentQuotient F) := rationalTorusUnipotentQuotientMeasure F with hm
  set f11 : RationalTorusUnipotentQuotient F → ℂ := fun q =>
    X0.indicator (fun _ => (1 : ℂ)) q.out *
      (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (adelicHeight F q.out) *
      (φ q.out * conj (ψ q.out)) with hf11
  set f12 : RationalTorusUnipotentQuotient F → ℂ := fun q =>
    X0.indicator (fun _ => (1 : ℂ)) q.out *
      (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (adelicHeight F q.out) *
      (φ q.out * conj (ψ₂ q.out)) with hf12
  set f21 : RationalTorusUnipotentQuotient F → ℂ := fun q =>
    X0.indicator (fun _ => (1 : ℂ)) q.out *
      (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (adelicHeight F q.out) *
      (φ₂ q.out * conj (ψ q.out)) with hf21
  set f22 : RationalTorusUnipotentQuotient F → ℂ := fun q =>
    X0.indicator (fun _ => (1 : ℂ)) q.out *
      (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (adelicHeight F q.out) *
      (φ₂ q.out * conj (ψ₂ q.out)) with hf22
  have hI11i : Integrable f11 m := hi11
  have hI12i : Integrable f12 m := hi12
  have hI21i : Integrable f21 m := hi21
  have hI22i : Integrable f22 m := hi22
  have hsplit : (∫ q : RationalTorusUnipotentQuotient F,
        X0.indicator (fun _ => (1 : ℂ)) q.out *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (adelicHeight F q.out) *
          (AutomorphicForm.constantTerm νb (fun t => AutomorphicForm.unipotentGL2 t) E q.out *
            conj (AutomorphicForm.constantTerm νb (fun t => AutomorphicForm.unipotentGL2 t) E' q.out)) ∂m)
      = (∫ q, f11 q ∂m) + (∫ q, f12 q ∂m) + (∫ q, f21 q ∂m) + (∫ q, f22 q ∂m) := by
    calc (∫ q : RationalTorusUnipotentQuotient F,
          X0.indicator (fun _ => (1 : ℂ)) q.out *
            (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (adelicHeight F q.out) *
            (AutomorphicForm.constantTerm νb (fun t => AutomorphicForm.unipotentGL2 t) E q.out *
              conj (AutomorphicForm.constantTerm νb (fun t => AutomorphicForm.unipotentGL2 t) E' q.out)) ∂m)
        = ∫ q, (f11 q + f12 q + f21 q + f22 q) ∂m := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
          simp only [hf11, hf12, hf21, hf22, hCTφ, hCTψ, map_add]
          ring
      _ = (∫ q, (f11 q + f12 q + f21 q) ∂m) + ∫ q, f22 q ∂m :=
          integral_add ((hI11i.add hI12i).add hI21i) hI22i
      _ = (∫ q, (f11 q + f12 q) ∂m) + (∫ q, f21 q ∂m) + ∫ q, f22 q ∂m := by
          congr 1
          exact integral_add (hI11i.add hI12i) hI21i
      _ = (∫ q, f11 q ∂m) + (∫ q, f12 q ∂m) + (∫ q, f21 q ∂m) + ∫ q, f22 q ∂m := by
          congr 2
          exact integral_add hI11i hI12i
  have hv11' : ∫ q, f11 q ∂m = _ := hv11
  have hv12' : ∫ q, f12 q ∂m = _ := hv12
  have hv21' : ∫ q, f21 q ∂m = _ := hv21
  have hv22' : ∫ q, f22 q ∂m = _ := hv22

  set X : ℂ := s + conj s' with hX
  have hXre : 1 < X.re := by
    simp only [hX, Complex.add_re, Complex.conj_re]; linarith
  have hX0 : X ≠ 0 := fun h => by rw [h, Complex.zero_re] at hXre; linarith
  have hnX0 : -X ≠ 0 := neg_ne_zero.2 hX0

  have hI11 : (∫ z in D, ∫ t in D,
        ((etaFst μ αm hαm s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν αm hαm s z : ℂˣ) : ℂ) *
              conj (((etaFst μ αm hαm s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν αm hαm s' z : ℂˣ) : ℂ)) *
            (Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
            (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
            (((ideleNorm F t)⁻¹ : ℝ) : ℂ) ∂νI ∂νI)
      = (Cs.toReal : ℂ) * Cn * ((Complex.exp ((R' : ℂ) * X) - Complex.exp ((R : ℂ) * X)) / X) := by
    rw [← band_integral F D D α β Cs hCstop hCs Cn hCnD X hX0 R R' hRR']
    refine setIntegral_congr_fun hDm fun z _ => setIntegral_congr_fun hDm fun t _ => ?_
    refine (integrand_eq (μ := μ) (ν := ν) (μ' := μ) (ν' := ν) hμ hν αm hαm s s' z t
      ((Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t))
      ((Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t))).trans ?_
    have h1 : ((μ t : ℂˣ) : ℂ) * ((μ t : ℂˣ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero _)
    have h2 : ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ)⁻¹ * ((ν z : ℂˣ) : ℂ)⁻¹ = 1 := by
      field_simp
    rw [h1, h2, one_mul, one_mul, hαI t, ← hX]
    ring

  have hI22 : (∫ z in D, ∫ t in D,
        ((etaFst ν αm hαm (-s) (z * t) : ℂˣ) : ℂ) * ((etaSnd μ αm hαm (-s) z : ℂˣ) : ℂ) *
              conj (((etaFst ν αm hαm (-s') (z * t) : ℂˣ) : ℂ) * ((etaSnd μ αm hαm (-s') z : ℂˣ) : ℂ)) *
            (Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
            (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
            (((ideleNorm F t)⁻¹ : ℝ) : ℂ) ∂νI ∂νI)
      = (Cs.toReal : ℂ) * Cn * ((Complex.exp ((R' : ℂ) * (-X)) - Complex.exp ((R : ℂ) * (-X))) / (-X)) := by
    rw [← band_integral F D D α β Cs hCstop hCs Cn hCnD (-X) hnX0 R R' hRR']
    refine setIntegral_congr_fun hDm fun z _ => setIntegral_congr_fun hDm fun t _ => ?_
    refine (integrand_eq (μ := ν) (ν := μ) (μ' := ν) (ν' := μ) hν hμ αm hαm (-s) (-s') z t
      ((Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t))
      ((Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t))).trans ?_
    have h1 : ((ν t : ℂˣ) : ℂ) * ((ν t : ℂˣ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero _)
    have h2 : ((ν z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ)⁻¹ * ((μ z : ℂˣ) : ℂ)⁻¹ = 1 := by
      field_simp
    have hnegX : -s + conj (-s') = -X := by rw [map_neg, hX]; ring
    rw [h1, h2, one_mul, one_mul, hαI t, hnegX]
    ring
  refine ⟨fun hμν hne => ?_, fun hμν => ?_⟩
  ·
    subst hμν
    set Y : ℂ := s - conj s' with hY
    have hY0 : Y ≠ 0 := sub_ne_zero.2 hne
    have hnY0 : -Y ≠ 0 := neg_ne_zero.2 hY0
    have hI12 : (∫ z in D, ∫ t in D,
          ((etaFst μ αm hαm s (z * t) : ℂˣ) : ℂ) * ((etaSnd μ αm hαm s z : ℂˣ) : ℂ) *
                conj (((etaFst μ αm hαm (-s') (z * t) : ℂˣ) : ℂ) * ((etaSnd μ αm hαm (-s') z : ℂˣ) : ℂ)) *
              (Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
              (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
              (((ideleNorm F t)⁻¹ : ℝ) : ℂ) ∂νI ∂νI)
        = (Cs.toReal : ℂ) * Cn * ((Complex.exp ((R' : ℂ) * Y) - Complex.exp ((R : ℂ) * Y)) / Y) := by
      rw [← band_integral F D D α β Cs hCstop hCs Cn hCnD Y hY0 R R' hRR']
      refine setIntegral_congr_fun hDm fun z _ => setIntegral_congr_fun hDm fun t _ => ?_
      refine (integrand_eq (μ := μ) (ν := μ) (μ' := μ) (ν' := μ) hμ hμ αm hαm s (-s') z t
        ((Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t))
        ((Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t))).trans ?_
      have h1 : ((μ t : ℂˣ) : ℂ) * ((μ t : ℂˣ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero _)
      have h2 : ((μ z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ)⁻¹ * ((μ z : ℂˣ) : ℂ)⁻¹ = 1 := by
        field_simp
      have hsY : s + conj (-s') = Y := by rw [map_neg, hY]; ring
      rw [h1, h2, one_mul, one_mul, hαI t, hsY]
      ring

    have hI21 : (∫ z in D, ∫ t in D,
          ((etaFst μ αm hαm (-s) (z * t) : ℂˣ) : ℂ) * ((etaSnd μ αm hαm (-s) z : ℂˣ) : ℂ) *
                conj (((etaFst μ αm hαm s' (z * t) : ℂˣ) : ℂ) * ((etaSnd μ αm hαm s' z : ℂˣ) : ℂ)) *
              (Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
              (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
              (((ideleNorm F t)⁻¹ : ℝ) : ℂ) ∂νI ∂νI)
        = (Cs.toReal : ℂ) * Cn * ((Complex.exp ((R' : ℂ) * (-Y)) - Complex.exp ((R : ℂ) * (-Y))) / (-Y)) := by
      rw [← band_integral F D D α β Cs hCstop hCs Cn hCnD (-Y) hnY0 R R' hRR']
      refine setIntegral_congr_fun hDm fun z _ => setIntegral_congr_fun hDm fun t _ => ?_
      refine (integrand_eq (μ := μ) (ν := μ) (μ' := μ) (ν' := μ) hμ hμ αm hαm (-s) s' z t
        ((Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t))
        ((Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t))).trans ?_
      have h1 : ((μ t : ℂˣ) : ℂ) * ((μ t : ℂˣ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero _)
      have h2 : ((μ z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ)⁻¹ * ((μ z : ℂˣ) : ℂ)⁻¹ = 1 := by
        field_simp
      have hsY : -s + conj s' = -Y := by rw [hY]; ring
      rw [h1, h2, one_mul, one_mul, hαI t, hsY]
      ring
    rw [hinc, hsplit, hv11', hv12', hv21', hv22', hI11, hI22, hI12, hI21]

    have hexp1 : Complex.exp ((R' : ℂ) * (-X)) = Complex.exp (-((R' : ℂ) * X)) := by rw [mul_neg]
    have hexp2 : Complex.exp ((R : ℂ) * (-X)) = Complex.exp (-((R : ℂ) * X)) := by rw [mul_neg]
    have hexp3 : Complex.exp ((R' : ℂ) * (-Y)) = Complex.exp (-((R' : ℂ) * Y)) := by rw [mul_neg]
    have hexp4 : Complex.exp ((R : ℂ) * (-Y)) = Complex.exp (-((R : ℂ) * Y)) := by rw [mul_neg]
    rw [hexp1, hexp2, hexp3, hexp4]
    push_cast
    field_simp
    ring
  ·
    obtain ⟨z₀, hz₀m, hz₀⟩ := hμν
    have hz₀1 : ideleNorm F z₀ = 1 := (NumberField.TateGlobal.mem_normOneIdeles_iff z₀).mp hz₀m
    have hχF : IsIdeleClassChar (𝓞 F) F (μ * ν⁻¹) := fun u => by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμF u, hνF u, inv_one, mul_one]
    have hχ : ∃ z : (𝔸)ˣ, ideleNorm F z = 1 ∧ (μ * ν⁻¹) z ≠ 1 :=
      ⟨z₀, hz₀1, fun h => hz₀ (mul_inv_eq_one.1 (by simpa using h))⟩
    have hχ'F : IsIdeleClassChar (𝓞 F) F (ν * μ⁻¹) := fun u => by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμF u, hνF u, inv_one, mul_one]
    have hχ' : ∃ z : (𝔸)ˣ, ideleNorm F z = 1 ∧ (ν * μ⁻¹) z ≠ 1 :=
      ⟨z₀, hz₀1, fun h => hz₀ (mul_inv_eq_one.1 (by simpa using h)).symm⟩
    have hI12 : (∫ z in D, ∫ t in D,
          ((etaFst μ αm hαm s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν αm hαm s z : ℂˣ) : ℂ) *
                conj (((etaFst ν αm hαm (-s') (z * t) : ℂˣ) : ℂ) * ((etaSnd μ αm hαm (-s') z : ℂˣ) : ℂ)) *
              (Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
              (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
              (((ideleNorm F t)⁻¹ : ℝ) : ℂ) ∂νI ∂νI) = 0 := by
      rw [← twisted_band_integral_eq_zero F D D hDF (μ * ν⁻¹) hχF hχ
        (fun z r => (((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ)⁻¹ * ((μ z : ℂˣ) : ℂ)⁻¹)
          * ((r : ℝ) : ℂ) ^ (s + conj (-s'))
          * (Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * r)
          * (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) r)]
      refine setIntegral_congr_fun hDm fun z _ => setIntegral_congr_fun hDm fun t _ => ?_
      refine (integrand_eq (μ := μ) (ν := ν) (μ' := ν) (ν' := μ) hν hμ αm hαm s (-s') z t
        ((Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t))
        ((Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t))).trans ?_
      rw [hαI t, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]

    have hI21 : (∫ z in D, ∫ t in D,
          ((etaFst ν αm hαm (-s) (z * t) : ℂˣ) : ℂ) * ((etaSnd μ αm hαm (-s) z : ℂˣ) : ℂ) *
                conj (((etaFst μ αm hαm s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν αm hαm s' z : ℂˣ) : ℂ)) *
              (Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
              (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
              (((ideleNorm F t)⁻¹ : ℝ) : ℂ) ∂νI ∂νI) = 0 := by
      rw [← twisted_band_integral_eq_zero F D D hDF (ν * μ⁻¹) hχ'F hχ'
        (fun z r => (((ν z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ)⁻¹ * ((ν z : ℂˣ) : ℂ)⁻¹)
          * ((r : ℝ) : ℂ) ^ (-s + conj s')
          * (Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * r)
          * (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) r)]
      refine setIntegral_congr_fun hDm fun z _ => setIntegral_congr_fun hDm fun t _ => ?_
      refine (integrand_eq (μ := ν) (ν := μ) (μ' := μ) (ν' := ν) hμ hν αm hαm (-s) s' z t
        ((Set.Icc α β).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t))
        ((Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t))).trans ?_
      rw [hαI t, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [hinc, hsplit, hv11', hv12', hv21', hv22', hI11, hI22, hI12, hI21]

    simp only [mul_zero, add_zero]
    have hexp1 : Complex.exp ((R' : ℂ) * (-X)) = Complex.exp (-((R' : ℂ) * X)) := by rw [mul_neg]
    have hexp2 : Complex.exp ((R : ℂ) * (-X)) = Complex.exp (-((R : ℂ) * X)) := by rw [mul_neg]
    rw [hexp1, hexp2]
    push_cast
    field_simp
    ring

end R1SlabINCBoth

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (s s' : ℂ) (_hs : 1 / 2 < s.re) (_hs' : 1 / 2 < s'.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ) (_hφK : AutomorphicForm.IsArchKFinite F φ) (_hφf : AutomorphicForm.IsKfSmooth F φ)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s') (AutomorphicForm.etaSnd ν αm hαm s') ψ)
      (_hψc : Continuous ψ) (_hψK : AutomorphicForm.IsArchKFinite F ψ) (_hψf : AutomorphicForm.IsKfSmooth F ψ),
    ∀ R R' : ℝ, R₀ ≤ R → R ≤ R' →
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x))
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F ψ) x))
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      (μ = ν → s ≠ conj s' →
      ((∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) -
       (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F))) =
      (c : ℂ) *
        (( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s + conj s'))) / (s + conj s')
          + (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s - conj s'))) / (s - conj s') ) -
         ( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s + conj s'))) / (s + conj s')
          + (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s - conj s'))) / (s - conj s') ))) ∧
      ((∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) →
      ((∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) -
       (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F))) =
      (c : ℂ) *
        (( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s + conj s'))) / (s + conj s') ) -
         ( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s + conj s'))) / (s + conj s') ))) := by
  intro αm hαm
  exact R1SlabINCBoth.main F α β hα hαβ hαm

end S_AutomorphicForm_exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_slab
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_slab (solution)
