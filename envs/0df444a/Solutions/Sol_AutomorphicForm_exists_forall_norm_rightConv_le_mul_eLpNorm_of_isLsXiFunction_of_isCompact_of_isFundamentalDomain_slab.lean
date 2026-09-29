-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8b2e50a2-5c31-5571-89ee-f44ab2490238

import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Data.Real.Sqrt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one"
p2m_attr_erase "simp" "AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add"

set_option autoImplicit false

noncomputable section

namespace R4CptSup

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.TateGlobal
open scoped ENNReal Pointwise
open MeasureTheory.Measure
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

variable (K : Type) [Field K] [NumberField K]

abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

abbrev Γ : Subgroup (AdelicGL2 (𝓞 K) K) := (globalPoints (𝓞 K) K).range

def slab (a b : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

variable {K}

scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

scoped instance instRightInv : (μ K).IsMulRightInvariant := isMulRightInvariant_adelicGLHaar K

scoped instance instSecondCountableGL : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

theorem normDet_mul (x z : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (x * z)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) * ideleNorm K (Matrix.GeneralLinearGroup.det z) := by
  rw [map_mul, ideleNorm_mul]

theorem det_centralScalar (a : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K a) = a ^ 2 := by
  rw [show centralScalar (𝓞 K) K = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem normDet_central (a : (AdeleRing (𝓞 K) K)ˣ) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K a)) = ideleNorm K a ^ 2 := by
  rw [det_centralScalar, pow_two, ideleNorm_mul, pow_two]

theorem normDet_global (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, ideleNorm_det_globalPoints, one_mul]

theorem central_comm (a : (AdeleRing (𝓞 K) K)ˣ) (X : AdelicGL2 (𝓞 K) K) :
    X * centralScalar (𝓞 K) K a = centralScalar (𝓞 K) K a * X := by
  refine Units.ext ?_
  show (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (a : AdeleRing (𝓞 K) K)
    = Matrix.scalar (Fin 2) (a : AdeleRing (𝓞 K) K) * (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
  exact ((Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq).symm

theorem exists_central_normDet_eq (t : ℝ) (ht : 0 < t) :
    ∃ a : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K a)) = t := by
  obtain ⟨a, -, ha⟩ := exists_ideleNorm_eq_and_snd_eq_one K (Real.sqrt t) (Real.sqrt_pos.2 ht)
  exact ⟨a, by rw [normDet_central, ha, Real.sq_sqrt ht.le]⟩

theorem slab_measurable (a b : ℝ) : MeasurableSet (slab K a b) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K a b

theorem Γ_smul (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) : γ • x = (γ : AdelicGL2 (𝓞 K) K) * x := rfl

theorem Γ_smul_eq (γ : Γ K) :
    ∃ γ₀ : Matrix.GeneralLinearGroup (Fin 2) K, (γ : AdelicGL2 (𝓞 K) K) = globalPoints (𝓞 K) K γ₀ := by
  obtain ⟨γ₀, h⟩ := γ.2
  exact ⟨γ₀, h.symm⟩

theorem slab_Γ_stable (a b : ℝ) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    γ • x ∈ slab K a b ↔ x ∈ slab K a b := by
  obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
  show ideleNorm K (Matrix.GeneralLinearGroup.det (_ * x)) ∈ Set.Icc a b ↔ x ∈ slab K a b
  rw [hγ₀, normDet_global]
  exact Iff.rfl

scoped instance instMeasurableConstSMulΓ : MeasurableConstSMul (Γ K) (AdelicGL2 (𝓞 K) K) :=
  ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩

theorem smulInvariant_restrict (S : Set (AdelicGL2 (𝓞 K) K))
    (hS : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), γ • x ∈ S ↔ x ∈ S) :
    SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict S) := by
  refine ⟨fun γ s hs => ?_⟩
  have hmeas : MeasurableSet ((fun x => γ • x) ⁻¹' s) := (measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)) hs
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => γ • x) ⁻¹' s ∩ S = (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ S) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [← Γ_smul γ x, hS γ x]
  rw [hset, measure_preimage_mul]

theorem countable_Γ : Countable (Γ K) := by
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    Function.Injective.countable fun _ _ h => Units.ext h
  have h : ((Γ K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

theorem finite_setOf_globalPoints_mem {Rc : Set (AdelicGL2 (𝓞 K) K)} (hRc : IsCompact Rc) :
    {γ : Matrix.GeneralLinearGroup (Fin 2) K | globalPoints (𝓞 K) K γ ∈ Rc}.Finite := by

  let e : Fin 2 → Fin 2 → AdelicGL2 (𝓞 K) K → AdeleRing (𝓞 K) K := fun i j g =>
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
  have he : ∀ i j, Continuous (e i j) := fun i j =>
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j
  have hfin : ∀ i j, {ξ : K | algebraMap K (AdeleRing (𝓞 K) K) ξ ∈ e i j '' Rc}.Finite := fun i j =>
    NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K (hRc.image (he i j))
  have hpi : (Set.univ.pi fun i : Fin 2 => Set.univ.pi fun j : Fin 2 =>
      {ξ : K | algebraMap K (AdeleRing (𝓞 K) K) ξ ∈ e i j '' Rc}).Finite :=
    Set.Finite.pi fun i => Set.Finite.pi fun j => hfin i j
  refine Set.Finite.of_finite_image (f := fun γ : Matrix.GeneralLinearGroup (Fin 2) K =>
    fun i j => (γ : Matrix (Fin 2) (Fin 2) K) i j) (hpi.subset ?_) ?_
  · rintro _ ⟨γ, hγ, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
    intro i j
    exact ⟨globalPoints (𝓞 K) K γ, hγ, rfl⟩
  · intro γ _ γ' _ h
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrFun (congrFun h i) j

theorem exists_setLIntegral_le_mul_of_isCompact (a b : ℝ) {Φ₀ : Set (AdelicGL2 (𝓞 K) K)}
    (hΦ₀ : Φ₀ ⊆ slab K a b) (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K a b)))
    {R' : Set (AdelicGL2 (𝓞 K) K)} (hR' : IsCompact R') (hR's : R' ⊆ slab K a b) :
    ∃ m : ℕ, ∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
      (∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), F (γ • x) = F x) →
        ∫⁻ x in R', F x ∂(μ K) ≤ m * ∫⁻ x in Φ₀, F x ∂(μ K) := by
  classical
  haveI := countable_Γ (K := K)
  haveI : SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict (slab K a b)) :=
    smulInvariant_restrict _ (slab_Γ_stable a b)

  have hRR : IsCompact (R' * R'⁻¹) := hR'.mul hR'.inv
  set Sfin := {γ : Matrix.GeneralLinearGroup (Fin 2) K | globalPoints (𝓞 K) K γ ∈ R' * R'⁻¹} with hSfin
  have hSfin_f : Sfin.Finite := finite_setOf_globalPoints_mem hRR
  set T : Set (Γ K) := {δ | (δ : AdelicGL2 (𝓞 K) K) ∈ R' * R'⁻¹} with hT
  have hT_f : T.Finite := by
    have himg : T ⊆ (fun γ₀ : Matrix.GeneralLinearGroup (Fin 2) K =>
        (⟨globalPoints (𝓞 K) K γ₀, γ₀, rfl⟩ : Γ K)) '' Sfin := by
      intro δ hδ
      obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq δ
      refine ⟨γ₀, ?_, Subtype.ext hγ₀.symm⟩
      show globalPoints (𝓞 K) K γ₀ ∈ R' * R'⁻¹
      rw [← hγ₀]
      exact hδ
    exact (hSfin_f.image _).subset himg
  refine ⟨hT_f.toFinset.card, fun F hFm hF => ?_⟩
  set m := hT_f.toFinset.card with hm
  set ν := (μ K).restrict (slab K a b) with hν

  have hcount : ∀ x : AdelicGL2 (𝓞 K) K,
      (∑' γ : Γ K, (γ • R').indicator F x) ≤ (m : ℝ≥0∞) * F x := by
    intro x
    set A : Set (Γ K) := {γ | x ∈ γ • R'} with hA
    by_cases hAe : A = ∅
    · have h0 : ∀ γ : Γ K, (γ • R').indicator F x = 0 := by
        intro γ
        have hγA : γ ∉ A := by rw [hAe]; exact Set.notMem_empty _
        have hx : x ∉ γ • R' := hγA
        exact Set.indicator_of_notMem hx F
      simp [h0]
    obtain ⟨γ₁, hγ₁⟩ := Set.nonempty_iff_ne_empty.2 hAe

    have hmap : ∀ γ ∈ A, γ₁⁻¹ * γ ∈ T := by
      intro γ hγ
      have h1 : (γ : AdelicGL2 (𝓞 K) K)⁻¹ * x ∈ R' := by
        obtain ⟨r, hr, hrx⟩ := Set.mem_smul_set.1 hγ
        rw [← hrx, Γ_smul, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hr
      have h2 : (γ₁ : AdelicGL2 (𝓞 K) K)⁻¹ * x ∈ R' := by
        obtain ⟨r, hr, hrx⟩ := Set.mem_smul_set.1 hγ₁
        rw [← hrx, Γ_smul, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hr
      show ((γ₁⁻¹ * γ : Γ K) : AdelicGL2 (𝓞 K) K) ∈ R' * R'⁻¹
      have : ((γ₁⁻¹ * γ : Γ K) : AdelicGL2 (𝓞 K) K) =
          ((γ₁ : AdelicGL2 (𝓞 K) K)⁻¹ * x) * ((γ : AdelicGL2 (𝓞 K) K)⁻¹ * x)⁻¹ := by
        push_cast
        group
      rw [this]
      exact Set.mul_mem_mul h2 (Set.inv_mem_inv.2 h1)
    have hA_f : A.Finite := by
      refine Set.Finite.of_finite_image (f := fun γ => γ₁⁻¹ * γ) (hT_f.subset ?_) ?_
      · rintro _ ⟨γ, hγ, rfl⟩
        exact hmap γ hγ
      · intro γ _ γ' _ h
        exact mul_left_cancel h
    have hA_card : hA_f.toFinset.card ≤ m := by
      rw [hm]
      have h := Finset.card_le_card_of_injOn (fun γ => γ₁⁻¹ * γ) (fun γ hγ =>
        hT_f.mem_toFinset.2 (hmap γ (hA_f.mem_toFinset.1 hγ))) (fun γ _ γ' _ h => mul_left_cancel h)
      exact h
    have hsum : (∑' γ : Γ K, (γ • R').indicator F x) = ∑ γ ∈ hA_f.toFinset, (γ • R').indicator F x := by
      refine tsum_eq_sum fun γ hγ => ?_
      have hγA : γ ∉ A := fun h => hγ (hA_f.mem_toFinset.2 h)
      have hx : x ∉ γ • R' := hγA
      exact Set.indicator_of_notMem hx F
    rw [hsum]
    calc ∑ γ ∈ hA_f.toFinset, (γ • R').indicator F x ≤ ∑ γ ∈ hA_f.toFinset, F x :=
          Finset.sum_le_sum fun γ _ => Set.indicator_le_self _ _ _
      _ = (hA_f.toFinset.card : ℝ≥0∞) * F x := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ≥0∞) * F x := mul_le_mul_of_nonneg_right (by exact_mod_cast hA_card) bot_le

  have h1 : ∫⁻ x in R', F x ∂ν = ∑' γ : Γ K, ∫⁻ x in γ • R' ∩ Φ₀, F (γ⁻¹ • x) ∂ν := hFD.setLIntegral_eq_tsum' F R'
  have h2 : ∀ γ : Γ K, ∫⁻ x in γ • R' ∩ Φ₀, F (γ⁻¹ • x) ∂ν = ∫⁻ x in Φ₀, (γ • R').indicator F x ∂ν := by
    intro γ
    have hmeas : MeasurableSet (γ • R') := by
      have : γ • R' = (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) '' R' := by
        ext y
        simp only [Set.mem_smul_set, Set.mem_image, Γ_smul]
      rw [this]
      exact (hR'.image (continuous_const.mul continuous_id)).isClosed.measurableSet
    simp_rw [hF]
    rw [lintegral_indicator hmeas, Measure.restrict_restrict hmeas]
  simp_rw [h2] at h1
  have h3 : (∑' γ : Γ K, ∫⁻ x in Φ₀, (γ • R').indicator F x ∂ν) =
      ∫⁻ x in Φ₀, ∑' γ : Γ K, (γ • R').indicator F x ∂ν := by
    refine (lintegral_tsum fun γ => ?_).symm
    have hmeas : MeasurableSet (γ • R') := by
      have : γ • R' = (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) '' R' := by
        ext y
        simp only [Set.mem_smul_set, Set.mem_image, Γ_smul]
      rw [this]
      exact (hR'.image (continuous_const.mul continuous_id)).isClosed.measurableSet
    exact (hFm.indicator hmeas).aemeasurable
  rw [h3] at h1

  have hR'ν : ∫⁻ x in R', F x ∂ν = ∫⁻ x in R', F x ∂(μ K) := by
    rw [hν, Measure.restrict_restrict' (slab_measurable a b), Set.inter_eq_left.2 hR's]
  have hΦν : ∀ G : AdelicGL2 (𝓞 K) K → ℝ≥0∞, ∫⁻ x in Φ₀, G x ∂ν = ∫⁻ x in Φ₀, G x ∂(μ K) := by
    intro G
    rw [hν, Measure.restrict_restrict' (slab_measurable a b), Set.inter_eq_left.2 hΦ₀]
  rw [← hR'ν, h1, hΦν, ← lintegral_const_mul' (m : ℝ≥0∞) _ (ENNReal.natCast_ne_top m)]
  exact lintegral_mono fun x => hcount x

theorem exists_setLIntegral_le_mul_of_isCompact' (a b : ℝ) (ha : 0 < a) (hab : a < b)
    {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} (hΦ₀ : Φ₀ ⊆ slab K a b)
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K a b)))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    {R : Set (AdelicGL2 (𝓞 K) K)} (hR : IsCompact R) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ u : AdelicGL2 (𝓞 K) K → ℂ, IsLsXiFunction (𝓞 K) K ⊤ ξ u → Continuous u →
      ∫⁻ x in R, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) ≤ ENNReal.ofReal N * ∫⁻ x in Φ₀, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) := by
  classical
  by_cases hRe : R = ∅
  · refine ⟨0, le_rfl, fun u _ _ => ?_⟩
    rw [hRe, Measure.restrict_empty, lintegral_zero_measure]
    exact bot_le
  have hRne : R.Nonempty := Set.nonempty_iff_ne_empty.2 hRe
  let nd : AdelicGL2 (𝓞 K) K → ℝ := fun z => ideleNorm K (Matrix.GeneralLinearGroup.det z)
  have nd_pos : ∀ z, 0 < nd z := fun z => ideleNorm_pos _
  have nd_cont : Continuous nd := continuous_ideleNorm_det K
  obtain ⟨w₁, hw₁, hmin⟩ := hR.exists_isMinOn hRne nd_cont.continuousOn
  obtain ⟨w₂, hw₂, hmax⟩ := hR.exists_isMaxOn hRne nd_cont.continuousOn
  set m₁ := nd w₁ with hm₁
  set m₂ := nd w₂ with hm₂
  have hm₁0 : 0 < m₁ := nd_pos w₁
  set ρ := b / a with hρ
  have hρ1 : 1 < ρ := (one_lt_div ha).2 hab
  obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt (m₂ / m₁) hρ1

  have hct : ∀ j : Fin N₀, ∃ aj : (AdeleRing (𝓞 K) K)ˣ,
      ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K aj)) = m₁ / a * ρ ^ (j : ℕ) :=
    fun j => exists_central_normDet_eq _ (mul_pos (div_pos hm₁0 ha) (pow_pos (zero_lt_one.trans hρ1) _))
  choose aj haj using hct
  let c : Fin N₀ → AdelicGL2 (𝓞 K) K := fun j => centralScalar (𝓞 K) K (aj j)
  let t : Fin N₀ → ℝ := fun j => m₁ / a * ρ ^ (j : ℕ)
  have ht : ∀ j, nd (c j) = t j := fun j => haj j
  have ht0 : ∀ j, 0 < t j := fun j => mul_pos (div_pos hm₁0 ha) (pow_pos (zero_lt_one.trans hρ1) _)

  let D : Fin N₀ → Set (AdelicGL2 (𝓞 K) K) := fun j => slab K (a * t j) (b * t j)
  have hcov : R ⊆ ⋃ j, R ∩ D j := by
    intro w hw
    have hr1 : m₁ ≤ nd w := hmin hw
    have hr2 : nd w ≤ m₂ := hmax hw
    have hx : 1 ≤ nd w / m₁ := (one_le_div hm₁0).2 hr1
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx hρ1
    have hnN : n < N₀ := by
      have h : ρ ^ n < ρ ^ N₀ := hn1.trans_lt ((div_le_div_of_nonneg_right hr2 hm₁0.le).trans_lt hN₀)
      exact (pow_lt_pow_iff_right₀ hρ1).1 h
    refine Set.mem_iUnion.2 ⟨⟨n, hnN⟩, hw, ?_⟩
    show nd w ∈ Set.Icc (a * (m₁ / a * ρ ^ n)) (b * (m₁ / a * ρ ^ n))
    have ha0 : a ≠ 0 := ha.ne'
    constructor
    · have e : a * (m₁ / a * ρ ^ n) = ρ ^ n * m₁ := by field_simp
      rw [e]
      exact (le_div_iff₀ hm₁0).1 hn1
    · have e : b * (m₁ / a * ρ ^ n) = ρ ^ (n + 1) * m₁ := by
        rw [pow_succ, hρ]
        ring
      rw [e]
      exact ((div_lt_iff₀ hm₁0).1 hn2).le

  let Rj : Fin N₀ → Set (AdelicGL2 (𝓞 K) K) := fun j => (fun x => x * c j) ⁻¹' (R ∩ D j)
  have hRj_c : ∀ j, IsCompact (Rj j) := by
    intro j
    have hcl : IsClosed (D j) := by
      show IsClosed (nd ⁻¹' Set.Icc (a * t j) (b * t j))
      exact isClosed_Icc.preimage nd_cont
    exact (Homeomorph.mulRight (c j)).isCompact_preimage.2 (hR.inter_right hcl)
  have hRj_s : ∀ j, Rj j ⊆ slab K a b := by
    intro j x hx
    have h := hx.2
    simp only [D, slab, Set.mem_setOf_eq, Set.mem_Icc, normDet_mul] at h
    rw [show ideleNorm K (Matrix.GeneralLinearGroup.det (c j)) = t j from ht j] at h
    exact ⟨le_of_mul_le_mul_right h.1 (ht0 j), le_of_mul_le_mul_right h.2 (ht0 j)⟩

  have hmul : ∀ j, ∃ m : ℕ, ∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
      (∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), F (γ • x) = F x) →
        ∫⁻ x in Rj j, F x ∂(μ K) ≤ m * ∫⁻ x in Φ₀, F x ∂(μ K) :=
    fun j => exists_setLIntegral_le_mul_of_isCompact a b hΦ₀ hFD (hRj_c j) (hRj_s j)
  choose mj hmj using hmul

  let κ : Fin N₀ → ℝ := fun j => ‖((ξ ⟨aj j, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ ^ 2 * mj j
  have hκ0 : ∀ j, 0 ≤ κ j := fun j => mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  refine ⟨∑ j, κ j, Finset.sum_nonneg fun j _ => hκ0 j, fun u hu huc => ?_⟩
  have hFm : Measurable fun x => (‖u x‖₊ : ℝ≥0∞) ^ 2 := (huc.measurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hFinv : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), (‖u (γ • x)‖₊ : ℝ≥0∞) ^ 2 = (‖u x‖₊ : ℝ≥0∞) ^ 2 := by
    intro γ x
    obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
    rw [Γ_smul, hγ₀, hu.left_invariant]

  have hpiece : ∀ j, ∫⁻ x in R ∩ D j, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) =
      ENNReal.ofReal (‖((ξ ⟨aj j, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ ^ 2) *
        ∫⁻ x in Rj j, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) := by
    intro j
    have hcv := (measurePreserving_mul_right (μ K) (c j)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.mulRight (c j)).measurableEmbedding (fun x => (‖u x‖₊ : ℝ≥0∞) ^ 2) (R ∩ D j)
    rw [← hcv]
    have h2 : ∀ x, (‖u (x * c j)‖₊ : ℝ≥0∞) ^ 2 =
        ENNReal.ofReal (‖((ξ ⟨aj j, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ ^ 2) * (‖u x‖₊ : ℝ≥0∞) ^ 2 := by
      intro x
      show (‖u (x * centralScalar (𝓞 K) K (aj j))‖₊ : ℝ≥0∞) ^ 2 = _
      rw [central_comm, hu.central_transform ⟨aj j, Subgroup.mem_top _⟩ x, nnnorm_mul, ENNReal.coe_mul,
        mul_pow, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rfl
    simp_rw [h2]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc ∫⁻ x in R, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K)
      ≤ ∫⁻ x in ⋃ j, R ∩ D j, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) := lintegral_mono_set hcov
    _ ≤ ∑' j, ∫⁻ x in R ∩ D j, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) := lintegral_iUnion_le _ _
    _ = ∑ j, ∫⁻ x in R ∩ D j, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) := tsum_fintype _
    _ ≤ ∑ j, ENNReal.ofReal (κ j) * ∫⁻ x in Φ₀, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [hpiece j]
        calc ENNReal.ofReal (‖((ξ ⟨aj j, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ ^ 2) *
              ∫⁻ x in Rj j, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K)
            ≤ ENNReal.ofReal (‖((ξ ⟨aj j, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ ^ 2) *
              (mj j * ∫⁻ x in Φ₀, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K)) :=
              mul_le_mul_of_nonneg_left (hmj j _ hFm hFinv) bot_le
          _ = ENNReal.ofReal (κ j) * ∫⁻ x in Φ₀, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) := by
              rw [← mul_assoc]
              congr 1
              show _ = ENNReal.ofReal (‖((ξ ⟨aj j, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ ^ 2 * mj j)
              rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (∑ j, κ j) * ∫⁻ x in Φ₀, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂(μ K) := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun j _ => hκ0 j]

theorem le_sqrt_mul_of_forall (r A Q : ℝ) (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (h : ∀ t : ℝ, 0 < t → r ≤ (t * A + t⁻¹ * Q) / 2) : r ≤ Real.sqrt A * Real.sqrt Q := by
  rcases hA.lt_or_eq with hA' | hA'
  · rcases hQ.lt_or_eq with hQ' | hQ'
    · set t := Real.sqrt Q / Real.sqrt A with ht
      have hsA := Real.sqrt_pos.2 hA'
      have hsQ := Real.sqrt_pos.2 hQ'
      have ht0 : 0 < t := div_pos hsQ hsA
      have h1 := h t ht0
      have e1 : t * A = Real.sqrt A * Real.sqrt Q := by
        rw [ht, div_mul_eq_mul_div, div_eq_iff hsA.ne',
          show Real.sqrt A * Real.sqrt Q * Real.sqrt A = Real.sqrt Q * (Real.sqrt A ^ 2) by ring,
          Real.sq_sqrt hA]
      have e2 : t⁻¹ * Q = Real.sqrt A * Real.sqrt Q := by
        rw [ht, inv_div, div_mul_eq_mul_div, div_eq_iff hsQ.ne',
          show Real.sqrt A * Real.sqrt Q * Real.sqrt Q = Real.sqrt A * (Real.sqrt Q ^ 2) by ring,
          Real.sq_sqrt hQ]
      rw [e1, e2] at h1
      linarith
    ·
      subst hQ'
      rw [Real.sqrt_zero, mul_zero]
      by_contra hr
      have hr' : 0 < r := lt_of_not_ge hr
      have h1 := h (r / A) (div_pos hr' hA')
      rw [mul_zero, add_zero, div_mul_cancel₀ r hA'.ne'] at h1
      linarith
  ·
    subst hA'
    rw [Real.sqrt_zero, zero_mul]
    by_contra hr
    have hr' : 0 < r := lt_of_not_ge hr
    rcases hQ.lt_or_eq with hQ' | hQ'
    · have h1 := h (Q / r) (div_pos hQ' hr')
      have e : (Q / r)⁻¹ * Q = r := by
        rw [inv_div]
        field_simp
      rw [mul_zero, zero_add, e] at h1
      linarith
    · subst hQ'
      have h1 := h 1 one_pos
      simp at h1
      linarith

end R4CptSup
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain_slab.R4CptSup"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain_slab.R4CptSup"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.TateGlobal
open scoped ENNReal Pointwise
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFD : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (C : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) :
    ∃ M : ℝ, ∀ u : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ,
      AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ u → Continuous u →
        MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) →
          ∀ x ∈ C, ‖AutomorphicForm.rightConv K u g x‖ ≤
            M * (eLpNorm u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀)).toReal := by
  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  have hΦ₀' : Φ₀ ⊆ R4CptSup.slab K α β := hΦ₀
  have hFD' : IsFundamentalDomain (R4CptSup.Γ K) Φ₀ ((R4CptSup.μ K).restrict (R4CptSup.slab K α β)) := hFD

  set S := tsupport g with hS
  have hSc : IsCompact S := hgc
  have hRc : IsCompact (C * S) := hC.mul hSc
  obtain ⟨N, hN0, hN⟩ := R4CptSup.exists_setLIntegral_le_mul_of_isCompact' α β hα hαβ hΦ₀' hFD' ξ hRc

  set Q : ℝ := ∫ z, ‖g z‖ ^ 2 ∂μ with hQ
  have hQ0 : 0 ≤ Q := integral_nonneg fun z => by positivity
  have hgc2 : HasCompactSupport (fun z => ‖g z‖ ^ 2) := by
    show HasCompactSupport ((fun r : ℝ => r ^ 2) ∘ fun z => ‖g z‖)
    exact hgc.norm.comp_left (zero_pow two_ne_zero)
  have hg2 : Integrable (fun z => ‖g z‖ ^ 2) μ := (hg.norm.pow 2).integrable_of_hasCompactSupport hgc2
  refine ⟨Real.sqrt N * Real.sqrt Q, fun u hu huc hu2 x hx => ?_⟩
  set nu : ℝ := (eLpNorm u 2 (μ.restrict Φ₀)).toReal with hnu
  have hnu0 : 0 ≤ nu := ENNReal.toReal_nonneg

  have hsqI : Integrable (fun y => ‖u y‖ ^ 2) (μ.restrict Φ₀) := (memLp_two_iff_integrable_sq_norm hu2.1).1 hu2
  have hnu_sq : nu ^ 2 = ∫ y in Φ₀, ‖u y‖ ^ 2 ∂μ := by
    have hI : 0 ≤ ∫ y in Φ₀, ‖u y‖ ^ 2 ∂μ := integral_nonneg fun y => by positivity
    rw [hnu, hu2.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
    simp only [Real.rpow_two]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _), ← Real.rpow_natCast, ← Real.rpow_mul hI]
    norm_num
  have hlin_Φ : ∫⁻ y in Φ₀, (‖u y‖₊ : ℝ≥0∞) ^ 2 ∂μ = ENNReal.ofReal (nu ^ 2) := by
    rw [hnu_sq, ofReal_integral_eq_lintegral_ofReal hsqI (Filter.Eventually.of_forall fun y => by positivity)]
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ((‖u y‖₊ : ℝ≥0∞) ^ 2) = ENNReal.ofReal (‖u y‖ ^ 2)
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rfl

  have huxc : Continuous fun z => u (x * z) := huc.comp (continuous_const.mul continuous_id)
  have hPint : IntegrableOn (fun z => ‖u (x * z)‖ ^ 2) S μ :=
    (huxc.norm.pow 2).continuousOn.integrableOn_compact hSc
  set P : ℝ := ∫ z in S, ‖u (x * z)‖ ^ 2 ∂μ with hP
  have hP0 : 0 ≤ P := integral_nonneg fun z => by positivity
  have hPle : P ≤ N * nu ^ 2 := by
    have h1 : ENNReal.ofReal P = ∫⁻ z in S, (‖u (x * z)‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
      rw [hP, ofReal_integral_eq_lintegral_ofReal hPint (Filter.Eventually.of_forall fun z => by positivity)]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show ENNReal.ofReal (‖u (x * z)‖ ^ 2) = ((‖u (x * z)‖₊ : ℝ≥0∞) ^ 2)
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rfl

    have h2 : ∫⁻ z in S, (‖u (x * z)‖₊ : ℝ≥0∞) ^ 2 ∂μ = ∫⁻ w in x • S, (‖u w‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
      have hcv := (measurePreserving_mul_left μ x).setLIntegral_comp_preimage_emb
        (MeasurableEquiv.mulLeft x).measurableEmbedding (fun w => (‖u w‖₊ : ℝ≥0∞) ^ 2) (x • S)
      have hpre : (fun z => x * z) ⁻¹' (x • S) = S := by
        rw [← Set.image_smul]
        exact Set.preimage_image_eq _ (mul_right_injective x)
      rw [hpre] at hcv
      exact hcv
    have h3 : x • S ⊆ C * S := by
      rintro _ ⟨z, hz, rfl⟩
      exact Set.mul_mem_mul hx hz
    have h4 : ENNReal.ofReal P ≤ ENNReal.ofReal (N * nu ^ 2) := by
      rw [h1, h2, ENNReal.ofReal_mul hN0, ← hlin_Φ]
      exact (lintegral_mono_set h3).trans (hN u hu huc)
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hN0 (sq_nonneg _))).1 h4

  have hint_ug : Integrable (fun z => u (x * z) * g z) μ :=
    (huxc.mul hg).integrable_of_hasCompactSupport hgc.mul_left
  have hbound : ∀ t : ℝ, 0 < t → ‖rightConv K u g x‖ ≤ (t * P + t⁻¹ * Q) / 2 := by
    intro t ht
    have hpt : ∀ z, ‖u (x * z) * g z‖ ≤ (t * (S.indicator (fun z => ‖u (x * z)‖ ^ 2) z) + t⁻¹ * ‖g z‖ ^ 2) / 2 := by
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, norm_mul]
        have htne : t ≠ 0 := ht.ne'
        have h2 : 2 * (‖u (x * z)‖ * ‖g z‖) ≤ t * ‖u (x * z)‖ ^ 2 + t⁻¹ * ‖g z‖ ^ 2 := by
          rw [← sub_nonneg]
          have e : t * ‖u (x * z)‖ ^ 2 + t⁻¹ * ‖g z‖ ^ 2 - 2 * (‖u (x * z)‖ * ‖g z‖) =
              (t * ‖u (x * z)‖ - ‖g z‖) ^ 2 / t := by
            field_simp
            ring
          rw [e]
          positivity
        linarith
      · have hg0 : g z = 0 := image_eq_zero_of_notMem_tsupport hz
        rw [hg0, mul_zero, norm_zero, Set.indicator_of_notMem hz]
        simp
    have hI1 : Integrable (fun z => S.indicator (fun z => ‖u (x * z)‖ ^ 2) z) μ :=
      hPint.integrable_indicator hSc.isClosed.measurableSet
    have hI2 : Integrable (fun z => (t * (S.indicator (fun z => ‖u (x * z)‖ ^ 2) z) + t⁻¹ * ‖g z‖ ^ 2) / 2) μ :=
      ((hI1.const_mul t).add (hg2.const_mul t⁻¹)).div_const 2
    calc ‖rightConv K u g x‖ = ‖∫ z, u (x * z) * g z ∂μ‖ := by rw [rightConv_apply]
      _ ≤ ∫ z, ‖u (x * z) * g z‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, (t * (S.indicator (fun z => ‖u (x * z)‖ ^ 2) z) + t⁻¹ * ‖g z‖ ^ 2) / 2 ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) hI2
            (Filter.Eventually.of_forall hpt)
      _ = (t * P + t⁻¹ * Q) / 2 := by
          rw [integral_div, integral_add (hI1.const_mul t) (hg2.const_mul t⁻¹), integral_const_mul,
            integral_const_mul, integral_indicator hSc.isClosed.measurableSet]

  have hbound' : ∀ t : ℝ, 0 < t → ‖rightConv K u g x‖ ≤ (t * (N * nu ^ 2) + t⁻¹ * Q) / 2 := fun t ht =>
    (hbound t ht).trans (by
      refine div_le_div_of_nonneg_right (add_le_add ?_ le_rfl) (by norm_num)
      exact mul_le_mul_of_nonneg_left hPle ht.le)
  have hfin := R4CptSup.le_sqrt_mul_of_forall _ _ _ (mul_nonneg hN0 (sq_nonneg _)) hQ0 hbound'
  calc ‖rightConv K u g x‖ ≤ Real.sqrt (N * nu ^ 2) * Real.sqrt Q := hfin
    _ = Real.sqrt N * Real.sqrt Q * nu := by
        rw [Real.sqrt_mul hN0, Real.sqrt_sq hnu0]
        ring

end S_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain_slab (solution)
