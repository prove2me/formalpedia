-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_canonicalTruncationDomain_inter_lt_adelicHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/da42ed38-4032-5b42-baf2-91baf5b3a85b

import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_exists_pos_forall_isFundamentalDomain_borelSubgroup_canonicalTruncationDomain_inter_lt_adelicHeight
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_isClosed_rationalTorusUnipotent
import Theorems.Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_canonicalTruncationDomain_inter_lt_adelicHeight
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.mem_inducedSectionSubmodule_iff M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicHeight NumberField.AdelicBox
open AutomorphicForm
open scoped Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace R1CuspVanish

section FD

variable {Γ : Type*} [Group Γ] {X : Type*} [MulAction Γ X] [MeasurableSpace X]

theorem nullMeasurableSet_of_restrict {μ : Measure X} {s E : Set X} (hs : NullMeasurableSet s (μ.restrict E))
    (hsE : s ⊆ E) (hE : MeasurableSet E) : NullMeasurableSet s μ := by
  obtain ⟨t, hts, htm, hteq⟩ := hs.exists_measurable_superset_ae_eq
  have h1 : (μ.restrict E) (t \ s) = 0 := (ae_eq_set.1 hteq).1
  rw [Measure.restrict_apply' hE] at h1
  refine (htm.inter hE).nullMeasurableSet.congr ?_
  rw [ae_eq_set]
  constructor
  · have : (t ∩ E) \ s = (t \ s) ∩ E := by
      ext x; simp only [Set.mem_diff, Set.mem_inter_iff]; tauto
    rw [this]; exact h1
  · have : s \ (t ∩ E) = ∅ := Set.diff_eq_empty.2 fun x hx => ⟨hts hx, hsE hx⟩
    rw [this]; exact measure_empty

theorem isFundamentalDomain_union {μ : Measure X} {E Ψ S₁ : Set X} (hE : MeasurableSet E)
    (hEstab : ∀ (γ : Γ) (x : X), γ • x ∈ E ↔ x ∈ E) (hΨE : Ψ ⊆ E)
    (hΨ : IsFundamentalDomain Γ Ψ (μ.restrict E)) (hS₁ : IsFundamentalDomain Γ S₁ μ) :
    IsFundamentalDomain Γ (Ψ ∪ (S₁ \ E)) μ := by
  have hΨm : NullMeasurableSet Ψ μ := nullMeasurableSet_of_restrict hΨ.nullMeasurableSet hΨE hE
  have hsmulΨ : ∀ γ : Γ, γ • Ψ ⊆ E := by
    intro γ x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hx
    exact (hEstab γ y).2 (hΨE hy)
  have hsmulD : ∀ γ : Γ, γ • (S₁ \ E) ⊆ Eᶜ := by
    intro γ x hx h
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hx
    exact hy.2 ((hEstab γ y).1 h)
  have hsmulD' : ∀ γ : Γ, γ • (S₁ \ E) ⊆ γ • S₁ := fun γ => Set.smul_set_mono Set.diff_subset
  refine
    { nullMeasurableSet := hΨm.union (hS₁.nullMeasurableSet.diff hE.nullMeasurableSet)
      ae_covers := ?_
      aedisjoint := ?_ }
  · rw [← Measure.restrict_add_restrict_compl (μ := μ) hE, ae_add_measure_iff]
    constructor
    · filter_upwards [hΨ.ae_covers] with x hx
      obtain ⟨γ, hγ⟩ := hx
      exact ⟨γ, Or.inl hγ⟩
    · have h1 : ∀ᵐ x ∂μ.restrict Eᶜ, x ∈ Eᶜ := ae_restrict_mem hE.compl
      have h2 : ∀ᵐ x ∂μ.restrict Eᶜ, ∃ γ : Γ, γ • x ∈ S₁ := ae_restrict_of_ae hS₁.ae_covers
      filter_upwards [h1, h2] with x hx hx'
      obtain ⟨γ, hγ⟩ := hx'
      exact ⟨γ, Or.inr ⟨hγ, fun h => hx ((hEstab γ x).1 h)⟩⟩
  · intro γ γ' hne
    have hA : μ (γ • Ψ ∩ γ' • Ψ) = 0 := by
      have h0 : μ.restrict E (γ • Ψ ∩ γ' • Ψ) = 0 := hΨ.aedisjoint hne
      rw [Measure.restrict_apply' hE] at h0
      exact measure_mono_null (fun x (hx : x ∈ γ • Ψ ∩ γ' • Ψ) => Set.mem_inter hx (hsmulΨ γ hx.1)) h0
    have hB : μ (γ • S₁ ∩ γ' • S₁) = 0 := hS₁.aedisjoint hne
    change μ (γ • (Ψ ∪ (S₁ \ E)) ∩ γ' • (Ψ ∪ (S₁ \ E))) = 0
    rw [Set.smul_set_union, Set.smul_set_union]
    refine measure_mono_null ?_ (measure_union_null hA hB)
    rintro x ⟨hx | hx, hx' | hx'⟩
    · exact Or.inl ⟨hx, hx'⟩
    · exact absurd (hsmulΨ γ hx) (hsmulD γ' hx')
    · exact absurd (hsmulΨ γ' hx') (hsmulD γ hx)
    · exact Or.inr ⟨hsmulD' γ hx, hsmulD' γ' hx'⟩

end FD

theorem exists_isFundamentalDomain_left {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) (hΓ : DiscreteTopology Γ) :
    ∃ S : Set G, MeasurableSet S ∧ ∀ μ : Measure G, IsFundamentalDomain Γ S μ := by
  obtain ⟨D, hDm, hD, -⟩ :=
    MeasureTheory.exists_measurableSet_isFundamentalDomain_op_of_discreteTopology Γ hΓ
  refine ⟨D⁻¹, hDm.inv, fun μ => IsFundamentalDomain.mk' hDm.inv.nullMeasurableSet fun x => ?_⟩
  obtain ⟨γ, hγ, huniq⟩ := hD x⁻¹
  refine ⟨γ⁻¹, ?_, ?_⟩
  · show ((γ⁻¹ : Γ) : G) * x ∈ D⁻¹
    rw [Set.mem_inv, Subgroup.coe_inv, mul_inv_rev, inv_inv]
    exact hγ
  · intro δ hδ
    change ((δ : Γ) : G) * x ∈ D⁻¹ at hδ
    rw [Set.mem_inv, mul_inv_rev] at hδ
    have := huniq δ⁻¹ (by simpa using hδ)
    rw [← this, inv_inv]

section Local

variable {L : Type*} [NormedField L]

private theorem coe_mul' (s g : GL (Fin 2) L) :
    ((s * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = (s : Matrix (Fin 2) (Fin 2) L) * (g : Matrix (Fin 2) (Fin 2) L) := rfl

theorem bottom_row_mul {s : GL (Fin 2) L} (h10 : (s : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (g : GL (Fin 2) L) (j : Fin 2) :
    ((s * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 j
      = (s : Matrix (Fin 2) (Fin 2) L) 1 1 * (g : Matrix (Fin 2) (Fin 2) L) 1 j := by
  rw [coe_mul', Matrix.mul_apply, Fin.sum_univ_two, h10]
  ring

theorem norm_det_mul_of_upper {s : GL (Fin 2) L} (h10 : (s : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (g : GL (Fin 2) L) :
    ‖((s * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det‖
      = ‖(s : Matrix (Fin 2) (Fin 2) L) 0 0‖ * ‖(s : Matrix (Fin 2) (Fin 2) L) 1 1‖
          * ‖(g : Matrix (Fin 2) (Fin 2) L).det‖ := by
  have hdets : (s : Matrix (Fin 2) (Fin 2) L).det
      = (s : Matrix (Fin 2) (Fin 2) L) 0 0 * (s : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero]
  rw [coe_mul', Matrix.det_mul, hdets, norm_mul, norm_mul]

theorem localHeight_mul_of_unipotent {s : GL (Fin 2) L} (h10 : (s : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) L) 0 0 = 1) (h11 : (s : Matrix (Fin 2) (Fin 2) L) 1 1 = 1)
    (g : GL (Fin 2) L) : WindowedSiegel.localHeight (s * g) = WindowedSiegel.localHeight g := by
  have hrow := WindowedSiegel.rowNormSq_scalar_entries_mul (z := (s : Matrix (Fin 2) (Fin 2) L) 1 1) h10 rfl g
  unfold WindowedSiegel.localHeight
  rw [norm_det_mul_of_upper h10, hrow, h00, h11, norm_one]
  ring

theorem finLocalHeight_mul_of_unipotent {s : GL (Fin 2) L} (h10 : (s : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) L) 0 0 = 1) (h11 : (s : Matrix (Fin 2) (Fin 2) L) 1 1 = 1)
    (g : GL (Fin 2) L) : finLocalHeight (s * g) = finLocalHeight g := by
  have hrow : rowMaxNorm ((s * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) L) := by
    unfold rowMaxNorm
    rw [bottom_row_mul h10 g 0, bottom_row_mul h10 g 1, h11, one_mul, one_mul]
  unfold finLocalHeight
  rw [norm_det_mul_of_upper h10, hrow, h00, h11, norm_one, one_mul, one_mul]

end Local

section Height

variable (K : Type) [Field K] [NumberField K]

theorem adelicHeight_unipotentGL2_mul (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    adelicHeight K (unipotentGL2 x * g) = adelicHeight K g := by
  unfold adelicHeight
  rw [map_mul, map_mul]
  congr 1
  · unfold WindowedSiegel.archHeight
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_mul, localHeight_mul_of_unipotent] <;> rfl
  · unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul, finLocalHeight_mul_of_unipotent] <;> rfl

theorem det_unipotentGL2 {R : Type*} [CommRing R] (x : R) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem unipotentGL2_mem_borelSubgroup {R : Type*} [CommRing R] (x : R) :
    unipotentGL2 x ∈ borelSubgroup R := by
  simp [mem_borelSubgroup_iff]

end Height

section Discrete

variable (K : Type) [Field K] [NumberField K]

theorem discreteTopology_of_le_range (B : Subgroup (AdelicGL2 (𝓞 K) K))
    (hB : B ≤ (globalPoints (𝓞 K) K).range) : DiscreteTopology B := by
  set gp := globalPoints (𝓞 K) K with hgp
  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 K) K)
  have hfin : {γ : GL (Fin 2) K | (1 : AdelicGL2 (𝓞 K) K)⁻¹ * gp γ * 1 ∈ C}.Finite :=
    AutomorphicForm.adelicKernelLocalFiniteness K C hCc 1 1
  set R : Set (AdelicGL2 (𝓞 K) K) := gp '' {γ | gp γ ∈ C ∧ gp γ ≠ 1} with hR
  have hRfin : R.Finite := by
    refine (hfin.subset ?_).image gp
    intro γ hγ
    simpa using hγ.1
  set U : Set (AdelicGL2 (𝓞 K) K) := interior C \ R with hU
  have hUo : IsOpen U := isOpen_interior.sdiff hRfin.isClosed
  have h1U : (1 : AdelicGL2 (𝓞 K) K) ∈ U := by
    refine ⟨mem_interior_iff_mem_nhds.2 hC1, ?_⟩
    rintro ⟨γ, ⟨-, hne⟩, h1⟩; exact hne h1
  have hkey : ∀ x ∈ gp.range, x ∈ U → x = 1 := by
    rintro _ ⟨γ, rfl⟩ ⟨hint, hnot⟩
    by_contra hne
    exact hnot ⟨γ, ⟨interior_subset hint, hne⟩, rfl⟩
  apply discreteTopology_of_isOpen_singleton_one
  have hset : ({1} : Set B) = ((↑) : B → AdelicGL2 (𝓞 K) K) ⁻¹' U := by
    ext b
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl; exact h1U
    · intro hb
      exact Subtype.ext (hkey b (hB b.2) hb)
  rw [hset]
  exact hUo.preimage continuous_subtype_val

end Discrete

section Main

variable (K : Type) [Field K] [NumberField K]

theorem measurable_constantTerm (ν : Measure (AdeleRing (𝓞 K) K)) [SFinite ν]
    {a : AdelicGL2 (𝓞 K) K → ℂ} (ha : Measurable a) :
    Measurable (constantTerm ν (fun x => unipotentGL2 x) a) := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  have hcont : Continuous fun p : AdelicGL2 (𝓞 K) K × AdeleRing (𝓞 K) K => unipotentGL2 p.2 * p.1 :=
    (AutomorphicForm.continuous_unipotentGL2.comp continuous_snd).mul continuous_fst
  have hF : StronglyMeasurable fun p : AdelicGL2 (𝓞 K) K × AdeleRing (𝓞 K) K => a (unipotentGL2 p.2 * p.1) :=
    (ha.comp hcont.measurable).stronglyMeasurable
  have := hF.integral_prod_right' (ν := ν)
  exact this.measurable

theorem main (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ (a d : AdelicGL2 (𝓞 K) K → ℂ), Measurable a → Measurable d →
        (∀ γ ∈ borelSubgroup K, ∀ g, a (globalPoints (𝓞 K) K γ * g) = a g) →
        (∀ γ ∈ borelSubgroup K, ∀ g, d (globalPoints (𝓞 K) K γ * g) = d g) →
        (∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), d (unipotentGL2 x * g) = d g) →
        IntegrableOn
          (fun g => (a g - constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
            (fun x => unipotentGL2 x) a g) * d g)
          (canonicalTruncationDomain K α β ∩ {g | T < adelicHeight K g}) (adelicGLHaar (Fin 2) (𝓞 K) K) →
        ∫ g in canonicalTruncationDomain K α β ∩ {g | T < adelicHeight K g},
            (a g - constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => unipotentGL2 x) a g) * d g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  obtain ⟨T₀, hT₀, hFD⟩ :=
    AutomorphicForm.exists_pos_forall_isFundamentalDomain_borelSubgroup_canonicalTruncationDomain_inter_lt_adelicHeight
      K α β hα hαβ
  obtain ⟨-, -, -, hΦslab, -⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  refine ⟨T₀, hT₀, fun T hT a d ha hd haB hdB hdN hint => ?_⟩

  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set gp : GL (Fin 2) K →* AdelicGL2 (𝓞 K) K := globalPoints (𝓞 K) K with hgp
  set B : Subgroup (AdelicGL2 (𝓞 K) K) := (borelSubgroup K).map gp with hB
  set Φ₀ := canonicalTruncationDomain K α β with hΦ₀
  set slab : Set (AdelicGL2 (𝓞 K) K) :=
    {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hslab
  set hi : Set (AdelicGL2 (𝓞 K) K) := {g | T < adelicHeight K g} with hhi
  set E : Set (AdelicGL2 (𝓞 K) K) := slab ∩ hi with hE
  set Ψ : Set (AdelicGL2 (𝓞 K) K) := Φ₀ ∩ hi with hΨ
  set ν : Measure (AdeleRing (𝓞 K) K) := ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K) with hν
  set aN : AdelicGL2 (𝓞 K) K → ℂ := constantTerm ν (fun x => unipotentGL2 x) a with haN
  set F : AdelicGL2 (𝓞 K) K → ℂ := fun g => (a g - aN g) * d g with hF
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SigmaFinite μ := inferInstance
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_cond_adelicBox K

  have hslab_m : MeasurableSet slab :=
    (NumberField.TateGlobal.continuous_ideleNorm_det K).measurable measurableSet_Icc
  have hhi_m : MeasurableSet hi :=
    measurableSet_lt measurable_const (NumberField.AdelicHeight.continuous_adelicHeight K).measurable
  have hE_m : MeasurableSet E := hslab_m.inter hhi_m
  have haN_m : Measurable aN := measurable_constantTerm K ν ha
  have hF_m : Measurable F := (ha.sub haN_m).mul hd
  have hΨE : Ψ ⊆ E := Set.inter_subset_inter_left _ hΦslab

  have haN_B : ∀ γ ∈ borelSubgroup K, ∀ g, aN (gp γ * g) = aN g := fun γ hγ g =>
    AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup K haB hγ g
  have haN_N : ∀ (x : AdeleRing (𝓞 K) K) g, aN (unipotentGL2 x * g) = aN g := fun x g =>
    AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul K
      (fun k h => haB _ (unipotentGL2_mem_borelSubgroup k) h) x g
  have hF_B : ∀ γ ∈ borelSubgroup K, ∀ g, F (gp γ * g) = F g := by
    intro γ hγ g
    simp only [hF]
    rw [haB γ hγ g, haN_B γ hγ g, hdB γ hγ g]
  have hE_B : ∀ γ ∈ borelSubgroup K, ∀ g, gp γ * g ∈ E ↔ g ∈ E := by
    intro γ hγ g
    simp only [hE, hslab, hhi, Set.mem_inter_iff, Set.mem_setOf_eq, map_mul,
      NumberField.TateGlobal.ideleNorm_mul, hgp, AutomorphicForm.ideleNorm_det_globalPoints, one_mul,
      NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_mem_borelSubgroup K hγ g]
  have hE_N : ∀ (x : AdeleRing (𝓞 K) K) g, unipotentGL2 x * g ∈ E ↔ g ∈ E := by
    intro x g
    simp only [hE, hslab, hhi, Set.mem_inter_iff, Set.mem_setOf_eq, map_mul, det_unipotentGL2, one_mul,
      adelicHeight_unipotentGL2_mul K x g]
  have hE_B' : ∀ (b : B) (g : AdelicGL2 (𝓞 K) K), b • g ∈ E ↔ g ∈ E := by
    rintro ⟨_, hb⟩ g
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hb
    exact hE_B γ hγ g

  have hΨfd : IsFundamentalDomain B Ψ (μ.restrict E) := hFD T hT
  haveI hBdisc : DiscreteTopology B := discreteTopology_of_le_range K B (Subgroup.map_le_range gp _)
  obtain ⟨S₁, hS₁m, hS₁⟩ := exists_isFundamentalDomain_left B hBdisc
  set S : Set (AdelicGL2 (𝓞 K) K) := Ψ ∪ (S₁ \ E) with hS
  have hSfd : IsFundamentalDomain B S μ := isFundamentalDomain_union hE_m hE_B' hΨE hΨfd (hS₁ μ)
  have hSE : S ∩ E = Ψ := by
    apply Set.Subset.antisymm
    · rintro x ⟨hx | hx, hxE⟩
      · exact hx
      · exact absurd hxE hx.2
    · exact fun x hx => ⟨Or.inl hx, hΨE hx⟩

  obtain ⟨hHaar, hRinv⟩ := AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant K
  haveI := hHaar
  haveI := hRinv
  have hbox := AutomorphicForm.isFundamentalDomain_boxSheet_rationalTorusUnipotent K
  obtain ⟨hBle, hBcnt, hTm, hTfd, hlin⟩ := hbox
  haveI : Countable B := hBcnt
  set H₂ := rationalTorusUnipotent K with hH₂
  set μH := rationalTorusUnipotentHaar K with hμH
  set jn : AdeleRing (𝓞 K) K → H₂ :=
    fun u => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u) with hjn
  set Tbox : Set H₂ := jn '' adelicBox K with hTbox
  have hjn_val : ∀ u, ((jn u : H₂) : AdelicGL2 (𝓞 K) K) = unipotentGL2 u := fun u => rfl
  have hjn_m : Measurable jn := by
    have h1 : Measurable fun u : AdeleRing (𝓞 K) K => (unipotentGL2 u : AdelicGL2 (𝓞 K) K) :=
      AutomorphicForm.continuous_unipotentGL2.measurable
    exact h1.subtype_mk

  set f : AdelicGL2 (𝓞 K) K → ℂ := E.indicator F with hf
  have hf_m : Measurable f := hF_m.indicator hE_m
  have hf_B : ∀ γ ∈ B, ∀ g : AdelicGL2 (𝓞 K) K, f (γ * g) = f g := by
    intro γ hγ g
    obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.1 hγ
    by_cases hg : g ∈ E
    · rw [hf, Set.indicator_of_mem hg, Set.indicator_of_mem ((hE_B γ₀ hγ₀ g).2 hg), hF_B γ₀ hγ₀ g]
    · rw [hf, Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((hE_B γ₀ hγ₀ g).1 h))]
  have hfin : ∫⁻ g in S, ‖f g‖ₑ ∂μ < ∞ := by
    have : ∫⁻ g in S, ‖f g‖ₑ ∂μ = ∫⁻ g in Ψ, ‖F g‖ₑ ∂μ := by
      simp_rw [hf, enorm_indicator_eq_indicator_enorm]
      rw [lintegral_indicator hE_m, Measure.restrict_restrict hE_m, Set.inter_comm, hSE]
    rw [this]
    have h2 := hint.2
    simpa [HasFiniteIntegral, hF, haN] using h2
  obtain ⟨-, -, hunfold⟩ :=
    HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out μ H₂
      (AutomorphicForm.isClosed_rationalTorusUnipotent K) μH B hBle f hf_m hf_B S hSfd Tbox hTfd hfin

  have hmeas_eq : μH.restrict Tbox =
      Measure.map jn ((((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K).restrict
        (adelicBox K)) := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply hjn_m hA, ← lintegral_indicator_one hA,
      hlin (A.indicator 1) (measurable_one.indicator hA)]
    have : (fun u => A.indicator (1 : H₂ → ℝ≥0∞) (jn u)) = (jn ⁻¹' A).indicator 1 := by
      funext u
      by_cases hu : jn u ∈ A
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (Set.mem_preimage.2 hu)]; rfl
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (fun h => hu (Set.mem_preimage.1 h))]
    rw [show (fun u => A.indicator (1 : H₂ → ℝ≥0∞) (Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)))
        = fun u => A.indicator (1 : H₂ → ℝ≥0∞) (jn u) from rfl, this,
      lintegral_indicator_one (hjn_m hA), Measure.restrict_apply (hjn_m hA)]
  have hρν : (((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K).restrict (adelicBox K) = ν := by
    rw [Measure.restrict_smul]
    rfl
  have hfib : ∀ g₀ : AdelicGL2 (𝓞 K) K, ∫ x in Tbox, f ((x : AdelicGL2 (𝓞 K) K) * g₀) ∂μH = 0 := by
    intro g₀
    have hφm : Measurable fun x : H₂ => f ((x : AdelicGL2 (𝓞 K) K) * g₀) :=
      hf_m.comp (measurable_subtype_coe.mul_const _)
    rw [hmeas_eq, integral_map hjn_m.aemeasurable hφm.aestronglyMeasurable, hρν]
    simp only [hjn_val]
    by_cases hg₀ : g₀ ∈ E
    · have hrew : ∀ u, f (unipotentGL2 u * g₀) = (a (unipotentGL2 u * g₀) - aN g₀) * d g₀ := by
        intro u
        rw [hf, Set.indicator_of_mem ((hE_N u g₀).2 hg₀), hF]
        simp only []
        rw [haN_N u g₀, hdN u g₀]
      simp_rw [hrew]
      rw [integral_mul_const]
      suffices h0 : ∫ u, (a (unipotentGL2 u * g₀) - aN g₀) ∂ν = 0 by rw [h0, zero_mul]
      by_cases hI : Integrable (fun u => a (unipotentGL2 u * g₀)) ν
      · rw [integral_sub hI (integrable_const _), integral_const, probReal_univ, one_smul, sub_eq_zero]
        simp [haN, constantTerm, constantTermIntegrand]
      · apply integral_undef
        intro hI'
        have h3 : Integrable (fun u => (a (unipotentGL2 u * g₀) - aN g₀) + aN g₀) ν :=
          (integrable_add_const_iff (c := aN g₀)).2 hI'
        simp only [sub_add_cancel] at h3
        exact hI h3
    · have hrew : ∀ u, f (unipotentGL2 u * g₀) = 0 := fun u =>
        Set.indicator_of_notMem (fun h => hg₀ ((hE_N u g₀).1 h)) _
      simp_rw [hrew]
      exact integral_zero _ _

  have hlhs : ∫ g in S, f g ∂μ = ∫ g in Ψ, F g ∂μ := by
    rw [hf, setIntegral_indicator hE_m, hSE]
  show ∫ g in Ψ, F g ∂μ = 0
  rw [← hlhs, hunfold]
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  exact ae_of_all _ fun q => hfib q.out

end Main

end R1CuspVanish

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ (a d : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ), Measurable a → Measurable d →
        (∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K,
          a (AutomorphicForm.globalPoints (𝓞 K) K γ * g) = a g) →
        (∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K,
          d (AutomorphicForm.globalPoints (𝓞 K) K γ * g) = d g) →
        (∀ (x : AdeleRing (𝓞 K) K) (g : AutomorphicForm.AdelicGL2 (𝓞 K) K),
          d (AutomorphicForm.unipotentGL2 x * g) = d g) →
        IntegrableOn
          (fun g => (a g - AutomorphicForm.constantTerm
              (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) a g) * d g)
          (AutomorphicForm.canonicalTruncationDomain K α β ∩ {g | T < NumberField.AdelicHeight.adelicHeight K g})
          (adelicGLHaar (Fin 2) (𝓞 K) K) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β ∩ {g | T < NumberField.AdelicHeight.adelicHeight K g},
            (a g - AutomorphicForm.constantTerm
                (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
                (fun x => AutomorphicForm.unipotentGL2 x) a g) * d g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 :=
  R1CuspVanish.main K α β hα hαβ

end S_AutomorphicForm_exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_canonicalTruncationDomain_inter_lt_adelicHeight
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_canonicalTruncationDomain_inter_lt_adelicHeight (solution)
