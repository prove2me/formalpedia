-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.lintegral_iwasawa_indicator_tsum_tsum_enorm_sub_eq_measure_mul_lintegral_of_sigmaInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/25889a1b-7477-508a-9e52-b3b34b47b581

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicKernel
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_iwasawa_indicator_tsum_tsum_enorm_sub_eq_measure_mul_lintegral_of_sigmaInvariant
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory NumberField
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace R1CentreAbsorb

open NumberField IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel NumberField.AdelicHeight

section Height

variable {K : Type*} [NormedField K]

theorem rowMaxNorm_scalar_entries_mul {s : GL (Fin 2) K} {z : K}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖z‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hbot : ∀ j : Fin 2,
      ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 j
        = z * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold rowMaxNorm
  rw [Matrix.GeneralLinearGroup.coe_mul, hbot 0, hbot 1, norm_mul, norm_mul,
    mul_max_of_nonneg _ _ (norm_nonneg z)]

theorem finLocalHeight_scalar_entries_mul {s : GL (Fin 2) K} {z : K} (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z) (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hdets : (s : Matrix (Fin 2) (Fin 2) K).det = z ^ 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdet : ‖((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖z‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hdets, norm_mul, norm_pow]
  have hz2 : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  unfold finLocalHeight
  rw [hdet, rowMaxNorm_scalar_entries_mul h10 h11 g, mul_pow,
    mul_div_mul_left _ _ hz2.ne']

variable (F : Type) [Field F] [NumberField F]

theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g := by
  have hcoe : ∀ i j : Fin 2, ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j = if i = j then (z : AdeleRing (𝓞 F) F) else 0 := by
    intro i j
    show Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) i j = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  unfold adelicHeight
  rw [map_mul, map_mul]
  congr 1
  · refine archHeight_scalar_entries_mul F (z := (z : AdeleRing (𝓞 F) F).1) (fun v => ?_) ?_ ?_ ?_ ?_ _
    · exact (Units.map ((archEval F v).comp (adeleArch (𝓞 F) F)).toMonoidHom z).ne_zero
    all_goals rw [glArch_apply, hcoe]; rfl
  · unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul]
    refine finLocalHeight_scalar_entries_mul (z := ((z : AdeleRing (𝓞 F) F).2) v) ?_ ?_ ?_ ?_ ?_ _
    · exact (Units.map ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)).toMonoidHom z).ne_zero
    all_goals rw [finComponent_apply, glFin_apply, hcoe]; rfl

end Height

end R1CentreAbsorb

open Polynomial

namespace R1CentreAbsorb

section Cells

open AutomorphicForm

variable {K : Type*} [Field K]

theorem X_sub_C_sq (a : K) : ((X - C a) ^ 2 : K[X]) = X ^ 2 - C (2 * a) * X + C (a ^ 2) := by
  rw [map_mul, map_pow, show (C (2 : K)) = 2 from map_ofNat C 2]; ring

theorem trace_det_of_charpoly_eq {M : Matrix (Fin 2) (Fin 2) K} {a : K} (h : M.charpoly = (X - C a) ^ 2) :
    M.trace = 2 * a ∧ M.det = a ^ 2 := by
  rw [Matrix.charpoly_fin_two, X_sub_C_sq] at h
  have h1 := congrArg (fun p : K[X] => p.coeff 1) h
  have h0 := congrArg (fun p : K[X] => p.coeff 0) h
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C, if_true,
    mul_one] at h1 h0
  norm_num at h1 h0
  exact ⟨h1, h0⟩

theorem isCentralType_smul_iff {M : Matrix (Fin 2) (Fin 2) K} {t : K} (ht : t ≠ 0) :
    IsCentralType (t • M) ↔ IsCentralType M := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨t⁻¹ * c, ?_⟩
    have := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => t⁻¹ • N) hc
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using this
  · rintro ⟨c, rfl⟩
    exact ⟨t * c, by rw [smul_smul]⟩

theorem isUnipotentType_smul {M : Matrix (Fin 2) (Fin 2) K} {t : K} (ht : t ≠ 0) (h : IsUnipotentType M) :
    IsUnipotentType (t • M) := by
  obtain ⟨hnc, a, ha⟩ := h
  obtain ⟨htr, hdet⟩ := trace_det_of_charpoly_eq ha
  refine ⟨(isCentralType_smul_iff ht).not.mpr hnc, t * a, ?_⟩
  rw [Matrix.charpoly_fin_two, Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin, htr, hdet, X_sub_C_sq,
    smul_eq_mul]
  congr 2 <;> [(congr 2; ring); (congr 1; ring)]

theorem isUnipotentType_smul_iff {M : Matrix (Fin 2) (Fin 2) K} {t : K} (ht : t ≠ 0) :
    IsUnipotentType (t • M) ↔ IsUnipotentType M := by
  refine ⟨fun h => ?_, isUnipotentType_smul ht⟩
  have := isUnipotentType_smul (inv_ne_zero ht) h
  rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this

theorem coe_mul_scalar (γ : GL (Fin 2) K) (t : Kˣ) :
    ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (t : K) • (γ : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.GeneralLinearGroup.coe_mul]
  show (γ : Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) (t : K) = _
  rw [← (Matrix.scalar_commute (t : K) (fun r' => mul_comm _ r') _).eq, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

theorem mul_scalar_mem_unipotentCell_iff (γ : GL (Fin 2) K) (t : Kˣ) :
    γ * Matrix.GeneralLinearGroup.scalar (Fin 2) t ∈ unipotentCell K ↔ γ ∈ unipotentCell K := by
  rw [mem_unipotentCell_iff, mem_unipotentCell_iff, coe_mul_scalar]
  exact isUnipotentType_smul_iff t.ne_zero

end Cells

section NormClasses

open LT.TwistedNorm AutomorphicForm

theorem sigmaPartialNorm_mul_of_mem_center {G : Type*} [Group G] (σ : G →* G) (x : G) {y : G}
    (hy : y ∈ Subgroup.center G) (r : ℕ) :
    sigmaPartialNorm σ (x * y) r = sigmaPartialNorm σ x r * sigmaPartialNorm σ y r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul]
      have hc := Subgroup.mem_center_iff.mp hy (σ (sigmaPartialNorm σ x r))
      calc x * y * (σ (sigmaPartialNorm σ x r) * σ (sigmaPartialNorm σ y r))
          = x * (y * σ (sigmaPartialNorm σ x r)) * σ (sigmaPartialNorm σ y r) := by group
        _ = x * (σ (sigmaPartialNorm σ x r) * y) * σ (sigmaPartialNorm σ y r) := by rw [hc]
        _ = x * σ (sigmaPartialNorm σ x r) * (y * σ (sigmaPartialNorm σ y r)) := by group

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem scalar_mem_center (s : Lˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ Subgroup.center (GL (Fin 2) L) := by
  rw [Subgroup.mem_center_iff]
  intro g
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (n := Fin 2) (s : L) (fun r' => mul_comm _ r')
    (g : Matrix (Fin 2) (Fin 2) L)).eq i) j |>.symm

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S) (s : Rˣ) :
    Matrix.GeneralLinearGroup.map σ (Matrix.GeneralLinearGroup.scalar (Fin 2) s) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ : R →* S) s) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show σ (Matrix.scalar (Fin 2) (s : R) i j) = Matrix.scalar (Fin 2) (σ (s : R)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem map_algebraMap_scalar (t : Kˣ) :
    Matrix.GeneralLinearGroup.map (algebraMap K L) (Matrix.GeneralLinearGroup.scalar (Fin 2) t) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) t) :=
  map_scalar (algebraMap K L) t

variable [FiniteDimensional K L] [IsGalois K L]

theorem sigmaNormPow_mul_scalar {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) (s : Lˣ) :
    sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L)
        (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s) =
      sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) δ *
        Matrix.GeneralLinearGroup.map (algebraMap K L)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm K : L →* K) s)) := by
  rw [sigmaNormPow_def, sigmaPartialNorm_mul_of_mem_center _ _ (scalar_mem_center s), ← sigmaNormPow_def,
    ← sigmaNormPow_def]
  congr 1
  have h := hom_sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Matrix.GeneralLinearGroup.map (σ : L →+* L))
    (Matrix.GeneralLinearGroup.scalar (Fin 2)) (fun x => (map_scalar (σ : L →+* L) x).symm) (Module.finrank K L) s
  rw [← h, map_algebraMap_scalar]
  congr 1
  ext
  rw [coe_sigmaNormPow_units_eq_algebraMap_norm hgen]
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
theorem isNormRep_of_isConj {σ : L ≃ₐ[K] L} {γ γ' : GL (Fin 2) K} {δ : GL (Fin 2) L}
    (h : IsNormRep σ γ δ) (hc : IsConj γ γ') : IsNormRep σ γ' δ := by
  obtain ⟨P, hP⟩ := h
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap K L) c⁻¹, ?_⟩
  rw [map_mul, map_mul, ← hP, map_inv]
  group

omit [FiniteDimensional K L] [IsGalois K L] in
theorem isNormRep_mul_scalar {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [FiniteDimensional K L] [IsGalois K L]
    {γ : GL (Fin 2) K} {δ : GL (Fin 2) L} (h : IsNormRep σ γ δ) (s : Lˣ) :
    IsNormRep σ (γ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm K : L →* K) s))
      (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, ?_⟩
  rw [sigmaNormPow_mul_scalar hgen, map_mul, ← hP]
  have hc := Subgroup.mem_center_iff.mp
    (scalar_mem_center (Units.map (algebraMap K L : K →* L) (Units.map (Algebra.norm K : L →* K) s))) P
  rw [← map_algebraMap_scalar] at hc
  simp only [mul_assoc, hc]

end NormClasses

section CuspIndex

open LT.TwistedNorm AutomorphicForm AutomorphicForm.TwistedBruhat

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem mul_scalar_mem_normUnipotentSet {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} (hδ : δ ∈ normUnipotentSet K L σ hgen) (s : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ normUnipotentSet K L σ hgen := by
  obtain ⟨γ, hγ, hcls⟩ := hδ
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj] at hcls
  have hrep : IsNormRep σ γ δ := isNormRep_of_isConj (isNormRep_normRep hgen δ) hcls
  refine ⟨_, ?_, normClassMap_mk_eq_of_isNormRep hgen (isNormRep_mul_scalar hgen hrep s)⟩
  exact (mul_scalar_mem_unipotentCell_iff γ _).mpr hγ

theorem scalar_apply_one_zero (s : Lˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  show Matrix.scalar (Fin 2) (s : L) 1 0 = 0
  simp [Matrix.scalar_apply]

theorem scalar_mem_borelSubgroup (s : Lˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ borelSubgroup L :=
  scalar_apply_one_zero s

theorem mul_scalar_mem_cuspIndex {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L}
    (hδ : δ ∈ normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L))) (s : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈
      normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L)) :=
  ⟨mul_scalar_mem_normUnipotentSet hgen hδ.1 s, (borelSubgroup L).mul_mem hδ.2 (scalar_mem_borelSubgroup s)⟩

theorem bijOn_mul_scalar_cuspIndex {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (s : Lˣ) :
    Set.BijOn (fun δ : GL (Fin 2) L => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s)
      (normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L)))
      (normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L))) := by
  refine ⟨fun δ hδ => mul_scalar_mem_cuspIndex hgen hδ s, fun δ _ δ' _ h => mul_right_cancel h, fun δ hδ => ?_⟩
  refine ⟨δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹, mul_scalar_mem_cuspIndex hgen hδ s⁻¹, ?_⟩
  simp only [map_inv, inv_mul_cancel_right]

end CuspIndex

end R1CentreAbsorb

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped Pointwise

namespace R1CentreAbsorb

section AdelicAlgebra

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L w * y = y * centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem mul_cs_left (g y : AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * (centralScalar (𝓞 L) L w * y) = centralScalar (𝓞 L) L w * (g * y) := by
  rw [← mul_assoc, ← centralScalar_comm, mul_assoc]

theorem centralScalar_principal (q : Lˣ) :
    centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show Matrix.scalar (Fin 2) (algebraMap L (AdeleRing (𝓞 L) L) (q : L)) i j =
    algebraMap L (AdeleRing (𝓞 L) L) (Matrix.scalar (Fin 2) (q : L) i j)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem unitsAct_principal (q : Lˣ) :
    D.unitsAct σ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (σ : L →* L) q) :=
  Units.ext (D.compat σ (q : L))

theorem sigmaAdelicAct_centralScalar_principal (q : Lˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q)) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ : L →* L) q)) := by
  rw [sigmaAdelicAct_centralScalar, unitsAct_principal, centralScalar_principal]

theorem sigmaAdelicAct_globalPoints' (g : GL (Fin 2) L) :
    sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L g) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) g) :=
  sigmaAdelicAct_globalPoints K L D σ g

theorem inv_cs_mul_conj (a : (AdeleRing (𝓞 L) L)ˣ) (x G Y : AdelicGL2 (𝓞 L) L) :
    (centralScalar (𝓞 L) L a * x)⁻¹ * G * sigmaAdelicAct K L D σ (Y * (centralScalar (𝓞 L) L a * x)) =
      x⁻¹ * G * sigmaAdelicAct K L D σ
        (Y * (centralScalar (𝓞 L) L (a * (D.unitsAct σ⁻¹ a)⁻¹) * x)) := by
  have ht : sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (a * (D.unitsAct σ⁻¹ a)⁻¹)) =
      sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L a) * (centralScalar (𝓞 L) L a)⁻¹ := by
    rw [sigmaAdelicAct_centralScalar, sigmaAdelicAct_centralScalar, map_mul, map_inv, map_mul, map_inv, map_inv]
    congr 3
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rw [map_mul, map_mul, map_mul, map_mul, ht, mul_inv_rev, ← map_inv]
  simp only [mul_assoc, mul_cs_left]

end AdelicAlgebra

end R1CentreAbsorb

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm
open scoped Pointwise ENNReal

namespace R1CentreAbsorb

section Fibres

open AutomorphicForm.TwistedBruhat NumberField.AdelicHeight

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

def Iset (s : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)}

def Jset (s : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L |
    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)}

def Kgen (T : Set (GL (Fin 2) L)) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∑ᶠ δ ∈ T, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * g))

def Tgen (T : Set (GL (Fin 2) L)) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  Set.indicator (highSet (adelicHeight L) (Real.exp R))
    (@constantTerm _ (adeleBorel (𝓞 L) L) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
      (fun t => unipotentGL2 t)
      (fun y => ∑ᶠ δ ∈ T, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y)))
    (centralScalar (𝓞 L) L z * g)

theorem Kgen_centralScalar_mul (T : Set (GL (Fin 2) L)) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z a : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) :
    Kgen K L D σ T φ z (centralScalar (𝓞 L) L a * g) = Kgen K L D σ T φ (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) g := by
  unfold Kgen
  refine finsum_mem_congr rfl fun δ _ => ?_
  rw [inv_cs_mul_conj]
  simp only [map_mul, map_inv, mul_assoc]

theorem Tgen_centralScalar_mul (T : Set (GL (Fin 2) L)) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (z a : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    Tgen K L D σ T R φ z (centralScalar (𝓞 L) L a * g) = Tgen K L D σ T R φ (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) g := by
  unfold Tgen
  have hmem : centralScalar (𝓞 L) L z * (centralScalar (𝓞 L) L a * g) ∈ highSet (adelicHeight L) (Real.exp R) ↔
      centralScalar (𝓞 L) L (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) * g ∈ highSet (adelicHeight L) (Real.exp R) := by
    rw [mem_highSet_iff, mem_highSet_iff, adelicHeight_centralScalar_mul, adelicHeight_centralScalar_mul,
      adelicHeight_centralScalar_mul]
  by_cases hx : centralScalar (𝓞 L) L z * (centralScalar (𝓞 L) L a * g) ∈ highSet (adelicHeight L) (Real.exp R)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mp hx)]
    unfold constantTerm constantTermIntegrand
    refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
    show (∑ᶠ δ ∈ T, φ ((centralScalar (𝓞 L) L a * g)⁻¹ * globalPoints (𝓞 L) L δ *
        sigmaAdelicAct K L D σ (unipotentGL2 n * (centralScalar (𝓞 L) L z * (centralScalar (𝓞 L) L a * g))))) =
      ∑ᶠ δ ∈ T, φ (g⁻¹ * globalPoints (𝓞 L) L δ *
        sigmaAdelicAct K L D σ (unipotentGL2 n * (centralScalar (𝓞 L) L (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) * g)))
    refine finsum_mem_congr rfl fun δ _ => ?_
    rw [← mul_assoc (unipotentGL2 n), inv_cs_mul_conj]
    simp only [map_mul, map_inv, mul_assoc]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.mpr h'))]

theorem mul_scalar_apply (δ : GL (Fin 2) L) (c : Lˣ) (i j : Fin 2) :
    ((δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
      (δ : Matrix (Fin 2) (Fin 2) L) i j * (c : L) := by
  rw [coe_mul_scalar, Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem bijOn_mul_scalar_Iset (s c : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) :
    Set.BijOn (fun δ : GL (Fin 2) L => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (Iset K L σ hgen s a) (Iset K L σ hgen (s * c) a) := by
  have hmaps : ∀ (s c : Lˣ), Set.MapsTo (fun δ : GL (Fin 2) L => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (Iset K L σ hgen s a) (Iset K L σ hgen (s * c) a) := by
    intro s c δ hδ
    obtain ⟨h1, h2, h3, h4⟩ := hδ
    refine ⟨mul_scalar_mem_normUnipotentSet hgen h1 c, ?_, ?_, ?_⟩
    · rw [mul_scalar_apply, h2, zero_mul]
    · rw [mul_scalar_apply, h3, Units.val_mul]
    · rw [mul_scalar_apply, h4, Units.val_mul]; ring
  refine ⟨hmaps s c, fun δ _ δ' _ h => mul_right_cancel h, fun δ hδ => ?_⟩
  refine ⟨δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹, ?_, by simp only [map_inv, inv_mul_cancel_right]⟩
  have h := hmaps (s * c) c⁻¹ hδ
  rwa [mul_inv_cancel_right] at h

theorem bijOn_mul_scalar_Jset (s c : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) :
    Set.BijOn (fun δ : GL (Fin 2) L => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (Jset K L s a) (Jset K L (s * c) a) := by
  have hmaps : ∀ (s c : Lˣ), Set.MapsTo (fun δ : GL (Fin 2) L => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (Jset K L s a) (Jset K L (s * c) a) := by
    intro s c δ hδ
    obtain ⟨h2, h3, h4⟩ := hδ
    refine ⟨?_, ?_, ?_⟩
    · rw [mul_scalar_apply, h2, zero_mul]
    · rw [mul_scalar_apply, h3, Units.val_mul]
    · rw [mul_scalar_apply, h4, Units.val_mul]; ring
  refine ⟨hmaps s c, fun δ _ δ' _ h => mul_right_cancel h, fun δ hδ => ?_⟩
  refine ⟨δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹, ?_, by simp only [map_inv, inv_mul_cancel_right]⟩
  have h := hmaps (s * c) c⁻¹ hδ
  rwa [mul_inv_cancel_right] at h

theorem Kgen_Iset_principal_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (q : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) (s : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) :
    Kgen K L D σ (Iset K L σ hgen s a) φ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) g =
      Kgen K L D σ (Iset K L σ hgen (s * Units.map (σ : L →* L) q) a) φ z g := by
  unfold Kgen
  refine finsum_mem_eq_of_bijOn _ (bijOn_mul_scalar_Iset K L σ hgen s (Units.map (σ : L →* L) q) a) fun δ _ => ?_
  rw [map_mul (centralScalar (𝓞 L) L), mul_assoc (centralScalar (𝓞 L) L _), map_mul (sigmaAdelicAct K L D σ),
    sigmaAdelicAct_centralScalar_principal, map_mul (globalPoints (𝓞 L) L)]
  simp only [mul_assoc]

theorem Tgen_Jset_principal_mul (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (q : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) (s : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) :
    Tgen K L D σ (Jset K L s a) R φ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) g =
      Tgen K L D σ (Jset K L (s * Units.map (σ : L →* L) q) a) R φ z g := by
  unfold Tgen
  have hmem : centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) * g ∈
        highSet (adelicHeight L) (Real.exp R) ↔
      centralScalar (𝓞 L) L z * g ∈ highSet (adelicHeight L) (Real.exp R) := by
    rw [mem_highSet_iff, mem_highSet_iff, map_mul, mul_assoc, adelicHeight_centralScalar_mul,
      adelicHeight_centralScalar_mul]
  by_cases hx : centralScalar (𝓞 L) L z * g ∈ highSet (adelicHeight L) (Real.exp R)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
    unfold constantTerm constantTermIntegrand
    refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
    show (∑ᶠ δ ∈ Jset K L s a, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
        (unipotentGL2 n * (centralScalar (𝓞 L) L (Units.map _ q * z) * g)))) =
      ∑ᶠ δ ∈ Jset K L (s * Units.map (σ : L →* L) q) a, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
        (unipotentGL2 n * (centralScalar (𝓞 L) L z * g)))
    rw [map_mul (centralScalar (𝓞 L) L), mul_assoc (centralScalar (𝓞 L) L _), mul_cs_left]
    refine finsum_mem_eq_of_bijOn _ (bijOn_mul_scalar_Jset K L s (Units.map (σ : L →* L) q) a) fun δ _ => ?_
    rw [map_mul (sigmaAdelicAct K L D σ), sigmaAdelicAct_centralScalar_principal, map_mul (globalPoints (𝓞 L) L)]
    simp only [mul_assoc]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.mp h'))]

def Gfun (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
    ‖Kgen K L D σ (Iset K L σ hgen s a) φ z g - Tgen K L D σ (Jset K L s a) R φ z g‖ₑ

theorem Gfun_centralScalar_mul (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z a : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) :
    Gfun K L D σ hgen R φ z (centralScalar (𝓞 L) L a * g) = Gfun K L D σ hgen R φ (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) g := by
  unfold Gfun
  simp_rw [Kgen_centralScalar_mul, Tgen_centralScalar_mul]

theorem Gfun_principal_mul (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (q : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) :
    Gfun K L D σ hgen R φ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) g =
      Gfun K L D σ hgen R φ z g := by
  unfold Gfun
  simp_rw [Kgen_Iset_principal_mul, Tgen_Jset_principal_mul]
  exact (Equiv.mulRight (Units.map (σ : L →* L) q)).tsum_eq fun s =>
    ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
      ‖Kgen K L D σ (Iset K L σ hgen s a) φ z g - Tgen K L D σ (Jset K L s a) R φ z g‖ₑ

end Fibres

section Fold

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

theorem countable_units : Countable Lˣ := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  exact Function.Injective.countable (f := (Units.val : Lˣ → L)) Units.val_injective

def toTop (G : Type*) [Group G] : G →* (⊤ : Subgroup G) where
  toFun z := ⟨z, Subgroup.mem_top z⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def Ffun {mZ : MeasurableSpace (AdeleRing (𝓞 L) L)ˣ} (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ∫⁻ z in ΩL, ‖((ξ' z : ℂˣ) : ℂ)‖ₑ * Gfun K L D σ hgen R φ z g ∂νZL

theorem Ffun_centralScalar_mul {mZ : MeasurableSpace (AdeleRing (𝓞 L) L)ˣ} [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsMulLeftInvariant] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hξt : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1)
    (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (a : (AdeleRing (𝓞 L) L)ˣ) (ha : ξ' (a * (D.unitsAct σ⁻¹ a)⁻¹) = 1)
    (g : AdelicGL2 (𝓞 L) L) :
    Ffun K L D σ hgen νZL ΩL ξ' R φ (centralScalar (𝓞 L) L a * g) = Ffun K L D σ hgen νZL ΩL ξ' R φ g := by
  unfold Ffun
  simp_rw [Gfun_centralScalar_mul]
  generalize ht : a * (D.unitsAct σ⁻¹ a)⁻¹ = t
  rw [ht] at ha
  set H : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞ := fun w => ‖((ξ' w : ℂˣ) : ℂ)‖ₑ * Gfun K L D σ hgen R φ w g with hH
  have hpt : ∀ z, ‖((ξ' z : ℂˣ) : ℂ)‖ₑ * Gfun K L D σ hgen R φ (z * t) g = H (t * z) := by
    intro z
    simp only [hH, mul_comm z t, map_mul, ha, one_mul]
  simp_rw [hpt]

  have h1 : ∫⁻ z in ΩL, H (t * z) ∂νZL = ∫⁻ w in t • ΩL, H w ∂νZL := by
    rw [← Set.image_smul]
    exact (measurePreserving_mul_left νZL t).setLIntegral_comp_emb (MeasurableEquiv.mulLeft t).measurableEmbedding H ΩL
  rw [h1]
  haveI : Countable (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range := by
    haveI := countable_units (L := L)
    exact (MonoidHom.rangeRestrict_surjective _).countable
  refine (hΩL.smul_of_comm t).setLIntegral_eq hΩL H fun r w => ?_
  obtain ⟨_, q, rfl⟩ := r
  show ‖((ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * w) : ℂˣ) : ℂ)‖ₑ *
      Gfun K L D σ hgen R φ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * w) g =
    ‖((ξ' w : ℂˣ) : ℂ)‖ₑ * Gfun K L D σ hgen R φ w g
  rw [map_mul, hξt, one_mul, Gfun_principal_mul]

end Fold

end R1CentreAbsorb

end

noncomputable section

namespace KcCentreRemovalL

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped ENNReal NNReal Topology Pointwise

section Topology

variable (F : Type) [Field F] [NumberField F]

theorem secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem continuous_det :
    Continuous fun g : AdelicGL2 (𝓞 F) F => Matrix.GeneralLinearGroup.det g := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · exact Units.continuous_coe_inv.matrix_det

theorem continuous_diagOne :
    Continuous (diagOne : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1]
    exact (Units.continuous_val.matrixVecCons continuous_const).matrix_diagonal
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]
    exact (Units.continuous_coe_inv.matrixVecCons continuous_const).matrix_diagonal

theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 F) F : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal fun _ : Fin 2 => (u : AdeleRing (𝓞 F) F)
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · show Continuous fun u : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal fun _ : Fin 2 => ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

theorem mul_centralScalar_comm (u : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    g * centralScalar (𝓞 F) F u = centralScalar (𝓞 F) F u * g := by
  refine Units.ext ?_
  show (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) * Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 F) F) =
    Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 F) F) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
  exact (Matrix.scalar_commute (u : AdeleRing (𝓞 F) F) (fun r => Commute.all _ r) _).symm.eq

theorem det_unipotentGL2 (x : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x : AdelicGL2 (𝓞 F) F) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, AutomorphicForm.unipotentGL2_coe, Matrix.det_fin_two_of]
  simp only [mul_one, mul_zero, sub_zero, Units.val_one]

theorem det_diagOne (t : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (diagOne t : AdelicGL2 (𝓞 F) F) = t := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1]).det = t
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem det_centralScalar (u : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F u) = u * u := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 F) F)).det = u * u
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]

theorem ideleNorm_det_maximalCompact (k : adelicMaximalCompact F) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) = 1 := by
  set f : adelicMaximalCompact F → ℝ := fun k =>
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) with hf
  have hfc : Continuous f :=
    (NumberField.TateGlobal.continuous_ideleNorm F).comp ((continuous_det F).comp continuous_subtype_val)
  have hpow : ∀ (k : adelicMaximalCompact F) (n : ℕ), f (k ^ n) = f k ^ n := by
    intro k n
    induction n with
    | zero =>
      simp only [pow_zero, hf, OneMemClass.coe_one, map_one]
      show NumberField.TateGlobal.ideleNorm F 1 = 1
      have h := NumberField.TateGlobal.ideleNorm_mul (F := F) 1 1
      rw [one_mul] at h
      have hpos := NumberField.TateGlobal.ideleNorm_pos (F := F) 1
      nlinarith
    | succ n ih =>
      rw [pow_succ, pow_succ, ← ih]
      simp only [hf, Subgroup.coe_mul, map_mul, NumberField.TateGlobal.ideleNorm_mul]
  have hinv : ∀ k : adelicMaximalCompact F, f k⁻¹ = (f k)⁻¹ := by
    intro k
    have h1 : f (k⁻¹ * k) = f k⁻¹ * f k := by
      simp only [hf, Subgroup.coe_mul, map_mul, NumberField.TateGlobal.ideleNorm_mul]
    rw [inv_mul_cancel] at h1
    have h0 : f 1 = 1 := by simpa using hpow 1 0
    rw [h0] at h1
    have hpos : 0 < f k := NumberField.TateGlobal.ideleNorm_pos _
    field_simp
    linarith [h1]
  obtain ⟨M, hM⟩ := (isCompact_range hfc).bddAbove
  have hbound : ∀ k : adelicMaximalCompact F, f k ≤ M := fun k => hM ⟨k, rfl⟩
  have hle : ∀ k : adelicMaximalCompact F, f k ≤ 1 := by
    intro k
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
    exact (lt_irrefl M) (hn.trans_le (by rw [← hpow]; exact hbound _))
  have hge : 1 ≤ f k := by
    have h := hle k⁻¹
    rw [hinv] at h
    have hpos : 0 < f k := NumberField.TateGlobal.ideleNorm_pos _
    exact (inv_le_one₀ hpos).mp h
  exact le_antisymm (hle k) hge

theorem ideleNorm_det_word (x : AdeleRing (𝓞 F) F) (u t : (AdeleRing (𝓞 F) F)ˣ)
    (k : adelicMaximalCompact F) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det
      (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
      NumberField.TateGlobal.ideleNorm F u ^ 2 * NumberField.TateGlobal.ideleNorm F t := by
  rw [map_mul, map_mul, map_mul, det_unipotentGL2, det_centralScalar, det_diagOne, one_mul,
    NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul,
    NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_maximalCompact, mul_one, sq]

end Topology

section Volume

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

theorem isFundamentalDomain_of_superset {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    {μ : Measure α} [SMulInvariantMeasure G α μ] {s t : Set α}
    (hs : IsFundamentalDomain G s μ) (hst : s ⊆ t) (htm : NullMeasurableSet t μ) (hae : t =ᵐ[μ] s) :
    IsFundamentalDomain G t μ where
  nullMeasurableSet := htm
  ae_covers := hs.ae_covers.mono fun _ ⟨g, hg⟩ => ⟨g, hst hg⟩
  aedisjoint := by
    intro a b hab
    have hN : μ (t \ s) = 0 := ae_le_set.mp hae.le
    have hsub : ∀ g : G, g • t ⊆ g • s ∪ g • (t \ s) := fun g => by
      rw [← Set.smul_set_union, Set.union_diff_cancel hst]
    refine measure_mono_null (Set.inter_subset_inter (hsub a) (hsub b)) ?_
    refine measure_mono_null (t := (a • s ∩ b • s) ∪ (a • (t \ s) ∪ b • (t \ s))) ?_ ?_
    · rintro x ⟨hxa | hxa, hxb | hxb⟩
      · exact Or.inl ⟨hxa, hxb⟩
      · exact Or.inr (Or.inr hxb)
      · exact Or.inr (Or.inl hxa)
      · exact Or.inr (Or.inl hxa)
    · exact measure_union_null (hs.aedisjoint hab)
        (measure_union_null (measure_smul_null hN a) (measure_smul_null hN b))

theorem smulInvariantMeasure_range (μ : Measure (AdeleRing (𝓞 F) F)ˣ) [μ.IsMulLeftInvariant] :
    SMulInvariantMeasure (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range
      (AdeleRing (𝓞 F) F)ˣ μ := by
  refine ⟨fun c s _ => ?_⟩
  exact measure_preimage_mul μ (c : (AdeleRing (𝓞 F) F)ˣ) s

def sqShell (α β r : ℝ) : Set (AdeleRing (𝓞 F) F)ˣ :=
  {u : (AdeleRing (𝓞 F) F)ˣ | NumberField.TateGlobal.ideleNorm F u ^ 2 * r ∈ Set.Icc α β}

variable {F} in
theorem mem_sqShell {α β r : ℝ} {u : (AdeleRing (𝓞 F) F)ˣ} :
    u ∈ sqShell F α β r ↔ NumberField.TateGlobal.ideleNorm F u ^ 2 * r ∈ Set.Icc α β := Iff.rfl

theorem measurableSet_sqShell (α β r : ℝ) : MeasurableSet (sqShell F α β r) :=
  (((NumberField.TateGlobal.continuous_ideleNorm F).pow 2).mul continuous_const).measurable
    measurableSet_Icc

theorem Icc_self_eq_iInter (α : ℝ) :
    Set.Icc α α = ⋂ n : ℕ, Set.Icc α (α + 1 / ((n : ℝ) + 1)) := by
  ext y
  simp only [Set.mem_Icc, Set.mem_iInter]
  constructor
  · rintro ⟨h1, h2⟩ n
    exact ⟨h1, h2.trans (le_add_of_nonneg_right (by positivity))⟩
  · intro h
    refine ⟨(h 0).1, le_of_forall_pos_le_add fun ε hε => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact (h n).2.trans (by linarith)

theorem exists_forall_measure_inter_sqShell_eq (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β)
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω
      (NumberField.Idele.idelicHaar F)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ, 0 < r → NumberField.Idele.idelicHaar F (Ω ∩ sqShell F α β r) = C := by
  haveI := smulInvariantMeasure_range F (NumberField.Idele.idelicHaar F)

  obtain ⟨Ω', hΩΩ', hΩ'm, hae⟩ := hΩ.nullMeasurableSet.exists_measurable_superset_ae_eq
  have hΩ' : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) Ω'
      (NumberField.Idele.idelicHaar F) :=
    isFundamentalDomain_of_superset hΩ hΩΩ' hΩ'm.nullMeasurableSet hae
  have hswap : ∀ S : Set (AdeleRing (𝓞 F) F)ˣ,
      NumberField.Idele.idelicHaar F (Ω ∩ S) = NumberField.Idele.idelicHaar F (Ω' ∩ S) := fun S =>
    measure_congr (hae.symm.inter (ae_eq_refl S))
  rcases hαβ.lt_or_eq with hlt | heq
  · obtain ⟨C, -, hCtop, hC⟩ :=
      NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const F Ω' hΩ'm hΩ' α β hα
        hlt
    exact ⟨C, hCtop, fun r hr => by rw [hswap]; exact hC r hr⟩
  · subst heq
    have hpos : ∀ n : ℕ, α < α + 1 / ((n : ℝ) + 1) := fun n => lt_add_of_pos_right _ (by positivity)
    choose C hC0 hCtop hC using fun n : ℕ =>
      NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const F Ω' hΩ'm hΩ' α
        (α + 1 / ((n : ℝ) + 1)) hα (hpos n)
    refine ⟨⨅ n, C n, ne_top_of_le_ne_top (hCtop 0) (iInf_le _ 0), fun r hr => ?_⟩
    rw [hswap]
    have hset : Ω' ∩ sqShell F α α r = ⋂ n : ℕ, (Ω' ∩ sqShell F α (α + 1 / ((n : ℝ) + 1)) r) := by
      rw [← Set.inter_iInter]
      congr 1
      ext u
      simp only [mem_sqShell, Set.mem_iInter, Icc_self_eq_iInter α]
    rw [hset]
    have hanti : Antitone fun n : ℕ => Ω' ∩ sqShell F α (α + 1 / ((n : ℝ) + 1)) r := by
      intro m n hmn
      refine Set.inter_subset_inter_right _ fun u hu => ⟨hu.1, hu.2.trans ?_⟩
      have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have h2 : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
      exact add_le_add_right (one_div_le_one_div_of_le h1 h2) _
    rw [hanti.measure_iInter (fun n => (hΩ'm.inter (measurableSet_sqShell F _ _ r)).nullMeasurableSet)
      ⟨0, by
        have h0 : NumberField.Idele.idelicHaar F (Ω' ∩ sqShell F α (α + 1 / ((0 : ℕ) + 1)) r) = C 0 :=
          hC 0 r hr
        rw [h0]; exact hCtop 0⟩]
    exact iInf_congr fun n => hC n r hr

end Volume

section Core

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

theorem sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar F) := by
  haveI := secondCountableTopology_idele F
  infer_instance

def detShell (α β : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

variable {F} in
theorem mem_detShell {α β : ℝ} {g : AdelicGL2 (𝓞 F) F} :
    g ∈ detShell F α β ↔ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β :=
  Iff.rfl

theorem measurable_weight :
    Measurable fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹ :=
  ENNReal.measurable_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F).measurable.inv

theorem measurable_integrand_fixed (Z : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (hZm : Measurable Z) (x : AdeleRing (𝓞 F) F) :
    Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      Z (unipotentGL2 x * diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F p.1)⁻¹ := by
  haveI := secondCountableTopology_idele F
  have hw : Continuous fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      unipotentGL2 x * diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F) :=
    (continuous_const.mul ((continuous_diagOne F).comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)
  exact (hZm.comp hw.measurable).mul ((measurable_weight F).comp measurable_fst)

theorem tonelli_shell (α β : ℝ) (C : ℝ≥0∞) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 F) F)ˣ)
    (hC : ∀ r : ℝ, 0 < r → NumberField.Idele.idelicHaar F (Ω₁ ∩ sqShell F α β r) = C)
    (H : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) (hHm : Measurable H) :
    (∫⁻ u in Ω₁, ∫⁻ t in Ω₂, (sqShell F α β (NumberField.TateGlobal.ideleNorm F t)).indicator (fun _ => (1 : ℝ≥0∞)) u * H t
        ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)) =
      C * ∫⁻ t in Ω₂, H t ∂(NumberField.Idele.idelicHaar F) := by
  haveI := secondCountableTopology_idele F
  haveI := sigmaFinite_idelicHaar F

  have hind : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ =>
      (sqShell F α β (NumberField.TateGlobal.ideleNorm F p.2)).indicator (fun _ => (1 : ℝ≥0∞)) p.1 := by
    have hset : MeasurableSet {p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ |
        NumberField.TateGlobal.ideleNorm F p.1 ^ 2 * NumberField.TateGlobal.ideleNorm F p.2 ∈ Set.Icc α β} :=
      ((((NumberField.TateGlobal.continuous_ideleNorm F).comp continuous_fst).pow 2).mul
        ((NumberField.TateGlobal.continuous_ideleNorm F).comp continuous_snd)).measurable measurableSet_Icc
    have heq : (fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ =>
        (sqShell F α β (NumberField.TateGlobal.ideleNorm F p.2)).indicator (fun _ => (1 : ℝ≥0∞)) p.1) =
        {p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ |
          NumberField.TateGlobal.ideleNorm F p.1 ^ 2 * NumberField.TateGlobal.ideleNorm F p.2 ∈
            Set.Icc α β}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext p
      classical
      simp only [Set.indicator_apply, sqShell, Set.mem_setOf_eq]
    rw [heq]
    exact measurable_const.indicator hset
  have hfm : Measurable (Function.uncurry fun (u t : (AdeleRing (𝓞 F) F)ˣ) =>
      (sqShell F α β (NumberField.TateGlobal.ideleNorm F t)).indicator (fun _ => (1 : ℝ≥0∞)) u * H t) :=
    hind.mul (hHm.comp measurable_snd)
  rw [lintegral_lintegral_swap hfm.aemeasurable]
  have hu : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      (∫⁻ u in Ω₁, (sqShell F α β (NumberField.TateGlobal.ideleNorm F t)).indicator (fun _ => (1 : ℝ≥0∞)) u * H t
        ∂(NumberField.Idele.idelicHaar F)) = C * H t := by
    intro t
    rw [lintegral_mul_const _ (measurable_const.indicator (measurableSet_sqShell F α β _)),
      lintegral_indicator_const (measurableSet_sqShell F α β _), one_mul,
      Measure.restrict_apply (measurableSet_sqShell F α β _), Set.inter_comm,
      hC _ (NumberField.TateGlobal.ideleNorm_pos t)]
  simp_rw [hu]
  rw [lintegral_const_mul _ hHm]

theorem core_fixed (α β : ℝ) (C : ℝ≥0∞) (Z : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (hZm : Measurable Z)
    (hZc : ∀ (u : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F), Z (centralScalar (𝓞 F) F u * g) = Z g)
    (Ω₁ Ω₂ : Set (AdeleRing (𝓞 F) F)ˣ)
    (hC : ∀ r : ℝ, 0 < r → NumberField.Idele.idelicHaar F (Ω₁ ∩ sqShell F α β r) = C)
    (x : AdeleRing (𝓞 F) F) :
    (∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
        (detShell F α β).indicator Z
            (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)) =
      C * ∫⁻ t in Ω₂, ∫⁻ k,
        Z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) := by

  have hpt : ∀ (u t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      (detShell F α β).indicator Z
          (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹ =
        (sqShell F α β (NumberField.TateGlobal.ideleNorm F t)).indicator (fun _ => (1 : ℝ≥0∞)) u *
          (Z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹) := by
    intro u t k
    have hword : unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F) =
        centralScalar (𝓞 F) F u * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 F) F)) := by
      rw [mul_centralScalar_comm F u (unipotentGL2 x)]
      simp only [mul_assoc]
    have hmem : (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) ∈
        detShell F α β ↔ u ∈ sqShell F α β (NumberField.TateGlobal.ideleNorm F t) := by
      rw [mem_detShell, mem_sqShell, ideleNorm_det_word]
    by_cases hu : u ∈ sqShell F α β (NumberField.TateGlobal.ideleNorm F t)
    · rw [Set.indicator_of_mem (hmem.mpr hu), Set.indicator_of_mem hu, one_mul, hword, hZc]
    · rw [Set.indicator_of_notMem (fun h => hu (hmem.mp h)), Set.indicator_of_notMem hu, zero_mul,
        zero_mul]
  simp_rw [hpt]
  have hk : ∀ (u t : (AdeleRing (𝓞 F) F)ˣ),
      (∫⁻ k, (sqShell F α β (NumberField.TateGlobal.ideleNorm F t)).indicator (fun _ => (1 : ℝ≥0∞)) u *
          (Z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹) ∂(maximalCompactHaar F)) =
        (sqShell F α β (NumberField.TateGlobal.ideleNorm F t)).indicator (fun _ => (1 : ℝ≥0∞)) u *
          ∫⁻ k, Z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹ ∂(maximalCompactHaar F) := by
    intro u t
    refine lintegral_const_mul' _ _ ?_
    classical
    rw [Set.indicator_apply]
    split_ifs <;> simp
  simp_rw [hk]
  have hG := measurable_integrand_fixed F Z hZm x
  exact tonelli_shell F α β C Ω₁ Ω₂ hC
    (fun t => ∫⁻ k, Z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹ ∂(maximalCompactHaar F))
    (hG.lintegral_prod_right' (ν := maximalCompactHaar F))

theorem core (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β)
    (Z : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (hZm : Measurable Z)
    (hZc : ∀ (u : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F), Z (centralScalar (𝓞 F) F u * g) = Z g)
    (X : Set (AdeleRing (𝓞 F) F)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ₁ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω₁
      (NumberField.Idele.idelicHaar F)) :
    (∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
        (detShell F α β).indicator Z
            (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
      ∂(adelicAddHaar (𝓞 F) F)) =
    NumberField.Idele.idelicHaar F (Ω₁ ∩ {u | NumberField.TateGlobal.ideleNorm F u ^ 2 ∈ Set.Icc α β}) *
    (∫⁻ x in X, ∫⁻ t in Ω₂, ∫⁻ k,
        Z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F)
      ∂(adelicAddHaar (𝓞 F) F)) := by

  obtain ⟨C, hCtop, hC⟩ := exists_forall_measure_inter_sqShell_eq F α β hα hαβ Ω₁ hΩ₁
  have hV : NumberField.Idele.idelicHaar F
      (Ω₁ ∩ {u | NumberField.TateGlobal.ideleNorm F u ^ 2 ∈ Set.Icc α β}) = C := by
    have h := hC 1 one_pos
    simpa only [sqShell, mul_one] using h
  rw [hV]
  simp_rw [core_fixed F α β C Z hZm hZc Ω₁ Ω₂ hC]
  exact lintegral_const_mul' _ _ hCtop

end Core

section Fold

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem continuous_comp_pair {X W P : Type} [TopologicalSpace X] [TopologicalSpace W] [TopologicalSpace P]
    (G : X → W → ℂ) (hG : Continuous fun q : X × W => G q.1 q.2) (a : P → X) (ha : Continuous a) (e : P → W)
    (he : Continuous e) : Continuous fun p : P => G (a p) (e p) :=
  hG.comp (ha.prodMk he)

theorem continuous_swap_pair {X Y W : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
    (G : Y → X → W) (hG : Continuous fun q : Y × X => G q.1 q.2) : Continuous fun p : X × Y => G p.2 p.1 :=
  hG.comp (continuous_snd.prodMk continuous_fst)

theorem continuous_comp_mul_triple {X Y V W : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace V] [TopologicalSpace W] [Mul X] [ContinuousMul X] (S : X → W) (hS : Continuous S)
    (U : V → X) (hU : Continuous U) (C : Y → X) (hC : Continuous C) :
    Continuous fun r : (X × Y) × V => S (U r.2 * (C r.1.2 * r.1.1)) :=
  hS.comp ((hU.comp continuous_snd).mul ((hC.comp (continuous_snd.comp continuous_fst)).mul
    (continuous_fst.comp continuous_fst)))

section Generic

variable (L : Type) [Field L] [NumberField L]

theorem exists_finite_forall_ne_zero_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ)
    {X Y : Set (AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ Γ : Set (GL (Fin 2) L), Γ.Finite ∧ ∀ x ∈ X, ∀ y ∈ Y, ∀ δ : GL (Fin 2) L,
      φ (x⁻¹ * globalPoints (𝓞 L) L δ * y) ≠ 0 → δ ∈ Γ := by
  have hC : IsCompact (X * tsupport φ * Y⁻¹) := (hX.mul hφs).mul hY.inv
  refine ⟨{δ | (1 : AdelicGL2 (𝓞 L) L)⁻¹ * globalPoints (𝓞 L) L δ * 1 ∈ X * tsupport φ * Y⁻¹},
    hfin _ hC 1 1, ?_⟩
  intro x hx y hy δ hδ
  have hmem : x⁻¹ * globalPoints (𝓞 L) L δ * y ∈ tsupport φ := subset_tsupport φ hδ
  have h : globalPoints (𝓞 L) L δ = x * (x⁻¹ * globalPoints (𝓞 L) L δ * y) * y⁻¹ := by group
  change (1 : AdelicGL2 (𝓞 L) L)⁻¹ * globalPoints (𝓞 L) L δ * 1 ∈ X * tsupport φ * Y⁻¹
  rw [inv_one, one_mul, mul_one, h]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx hmem) (Set.inv_mem_inv.mpr hy)

theorem finsum_mem_eq_sum_of_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ) (T : Set (GL (Fin 2) L))
    {X Y : Set (AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ t : Finset (GL (Fin 2) L), (t : Set (GL (Fin 2) L)) ⊆ T ∧ ∀ x ∈ X, ∀ y ∈ Y,
      ∑ᶠ δ ∈ T, φ (x⁻¹ * globalPoints (𝓞 L) L δ * y) = ∑ δ ∈ t, φ (x⁻¹ * globalPoints (𝓞 L) L δ * y) := by
  obtain ⟨Γ, hΓ, hmem⟩ := exists_finite_forall_ne_zero_mem L hfin φ hφs hX hY
  have hΓT : (Γ ∩ T).Finite := hΓ.subset Set.inter_subset_left
  refine ⟨hΓT.toFinset, fun δ hδ => (hΓT.mem_toFinset.mp hδ).2, fun x hx y hy => ?_⟩
  apply finsum_mem_eq_sum_of_subset
  · rintro δ ⟨hδT, hδs⟩
    exact hΓT.mem_toFinset.mpr ⟨hmem x hx y hy δ hδs, hδT⟩
  · intro δ hδ
    exact (hΓT.mem_toFinset.mp hδ).2

theorem continuous_finsum_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (T : Set (GL (Fin 2) L)) :
    Continuous fun p : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L =>
      ∑ᶠ δ ∈ T, φ (p.1⁻¹ * globalPoints (𝓞 L) L δ * p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨X, hX, hXn⟩ := exists_compact_mem_nhds p.1
  obtain ⟨Y, hY, hYn⟩ := exists_compact_mem_nhds p.2
  obtain ⟨t, -, ht⟩ := finsum_mem_eq_sum_of_mem L hfin φ hφs T hX hY
  have hsum : Continuous fun q : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L =>
      ∑ δ ∈ t, φ (q.1⁻¹ * globalPoints (𝓞 L) L δ * q.2) := by
    refine continuous_finsetSum t fun δ _ => hφc.comp ?_
    exact (continuous_fst.inv.mul continuous_const).mul continuous_snd
  refine ((hsum.continuousOn (s := X ×ˢ Y)).congr fun q hq => ht q.1 hq.1 q.2 hq.2).continuousAt ?_
  exact prod_mem_nhds hXn hYn

end Generic

section Twisted

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem continuous_glMap {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B)
    (hf : Continuous f) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

theorem continuous_sigmaAdelicAct : Continuous (sigmaAdelicAct K L D σ) :=
  continuous_glMap (D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom (D.continuous_act σ)

theorem continuous_sigmaAdelicAct_centralScalar_mul :
    Continuous fun q : (AdeleRing (𝓞 L) L)ˣ × AdelicGL2 (𝓞 L) L =>
      sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L q.1 * q.2) :=
  (continuous_sigmaAdelicAct K L D σ).comp (((continuous_centralScalar L).comp continuous_fst).mul continuous_snd)

theorem continuous_fold (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (T' : Set (GL (Fin 2) L)) :
    Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∑ᶠ δ ∈ T', φ (p.1⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L p.2 * p.1)) :=
  continuous_comp_pair
    (fun g w : AdelicGL2 (𝓞 L) L => ∑ᶠ δ ∈ T', φ (g⁻¹ * globalPoints (𝓞 L) L δ * w))
    (continuous_finsum_mem L hloc φ hφc hφs T') Prod.fst continuous_fst
    (fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L p.2 * p.1))
    (continuous_swap_pair
      (fun (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) => sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * g))
      (continuous_sigmaAdelicAct_centralScalar_mul K L D σ))

theorem continuous_truncationIntegrand (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (T' : Set (GL (Fin 2) L)) :
    Continuous fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
      ∑ᶠ δ ∈ T',
        φ (r.1.1⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
          (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1))) :=
  continuous_comp_pair
    (fun g w : AdelicGL2 (𝓞 L) L => ∑ᶠ δ ∈ T', φ (g⁻¹ * globalPoints (𝓞 L) L δ * w))
    (continuous_finsum_mem L hloc φ hφc hφs T')
    (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L => r.1.1)
    (continuous_fst.comp continuous_fst)
    (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
      sigmaAdelicAct K L D σ (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1)))
    (continuous_comp_mul_triple (sigmaAdelicAct K L D σ) (continuous_sigmaAdelicAct K L D σ)
      (fun q : AdeleRing (𝓞 L) L => (unipotentGL2 q : AdelicGL2 (𝓞 L) L))
      (AutomorphicForm.continuous_unipotentGL2 (R := AdeleRing (𝓞 L) L)) (centralScalar (𝓞 L) L)
      (continuous_centralScalar L))

open Classical in

theorem Tgen_eq_ite (T' : Set (GL (Fin 2) L)) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) :
    R1CentreAbsorb.Tgen K L D σ T' R φ z g =
      if Real.exp R < NumberField.AdelicHeight.adelicHeight L (centralScalar (𝓞 L) L z * g) then
        ∫ q, ∑ᶠ δ ∈ T',
          φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
            (unipotentGL2 q * (centralScalar (𝓞 L) L z * g)))
          ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
      else 0 := by
  unfold R1CentreAbsorb.Tgen
  rw [Set.indicator_apply]
  rfl

theorem measurable_Kgen_sub_Tgen [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (R : ℝ) (T' T'' : Set (GL (Fin 2) L)) :
    Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      R1CentreAbsorb.Kgen K L D σ T' φ p.2 p.1 - R1CentreAbsorb.Tgen K L D σ T'' R φ p.2 p.1 := by
  classical
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  haveI : IsFiniteMeasure
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) := inferInstance
  have hKm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      R1CentreAbsorb.Kgen K L D σ T' φ p.2 p.1 :=
    (continuous_fold K L D σ hloc φ hφc hφs T').measurable
  have hhigh : MeasurableSet {p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ |
      Real.exp R < NumberField.AdelicHeight.adelicHeight L (centralScalar (𝓞 L) L p.2 * p.1)} :=
    ((NumberField.AdelicHeight.continuous_adelicHeight L).comp
      (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst)).measurable measurableSet_Ioi
  have hCT : StronglyMeasurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∫ q, (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
        ∑ᶠ δ ∈ T'',
          φ (r.1.1⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
            (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1)))) (p, q)
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) :=
    (continuous_truncationIntegrand K L D σ hloc φ hφc hφs T'').stronglyMeasurable.integral_prod_right'
  have hTm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      R1CentreAbsorb.Tgen K L D σ T'' R φ p.2 p.1 := by
    simp_rw [Tgen_eq_ite]
    exact Measurable.ite hhigh hCT.measurable measurable_const
  exact hKm.sub hTm

set_option linter.deprecated false in

theorem measurable_Ffun [IsGalois K L] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' z : ℂˣ) : ℂ))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ) :
    Measurable (R1CentreAbsorb.Ffun K L D σ hgen νZL ΩL ξ' R φ) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  haveI : SigmaFinite νZL := inferInstance
  haveI : Countable Lˣ := R1CentreAbsorb.countable_units L
  have hG : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      R1CentreAbsorb.Gfun K L D σ hgen R φ p.2 p.1 := by
    unfold R1CentreAbsorb.Gfun
    refine Measurable.ennreal_tsum fun s => Measurable.ennreal_tsum fun a => ?_
    exact (measurable_Kgen_sub_Tgen K L D σ (AutomorphicForm.adelicKernelLocalFiniteness L) φ hφc hφs R _ _).enorm
  have h : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ‖((ξ' p.2 : ℂˣ) : ℂ)‖ₑ * R1CentreAbsorb.Gfun K L D σ hgen R φ p.2 p.1 :=
    (hξc.comp continuous_snd).measurable.enorm.mul hG
  exact h.lintegral_prod_right' (ν := νZL.restrict ΩL)

end Twisted

end Fold

end KcCentreRemovalL

end

section Solution

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ₁ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₁ (NumberField.Idele.idelicHaar L)) :
    (∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
            Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫⁻ z in ΩL, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                  φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L z * g))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                    φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L z * g)‖ₑ ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) =
      NumberField.Idele.idelicHaar L (Ω₁ ∩ {u | NumberField.TateGlobal.ideleNorm L u ^ 2 ∈ Set.Icc α β}) *
      (∫⁻ x in X, ∫⁻ t in Ω₂, ∫⁻ k,
            (∫⁻ z in ΩL, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L z * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L z * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) := by
  set ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := ξL.comp (R1CentreAbsorb.toTop (AdeleRing (𝓞 L) L)ˣ) with hξ'
  have hξ'_apply : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' z = ξL ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  have hξt' : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1 :=
    fun q => (hξ'_apply _).trans (hξt _ ⟨q, rfl⟩)
  have hξc' : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' z : ℂˣ) : ℂ) := hξc

  have hone : ∀ u : (AdeleRing (𝓞 L) L)ˣ, ξ' (u * (D.unitsAct σ⁻¹ u)⁻¹) = 1 := by
    intro u
    have hu : D.unitsAct σ (D.unitsAct σ⁻¹ u) = u := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have hσu : ξ' (D.unitsAct σ⁻¹ u) = ξ' u := by
      rw [hξ'_apply, hξ'_apply]
      have h := hξσ (D.unitsAct σ⁻¹ u)
      rw [hu] at h
      exact h.symm
    rw [map_mul, map_inv, hσu, mul_inv_cancel]
  exact KcCentreRemovalL.core L α β hα hαβ (R1CentreAbsorb.Ffun K L D σ hgen νZL ΩL ξ' R φ)
    (KcCentreRemovalL.measurable_Ffun K L D σ νZL ΩL hgen ξ' hξc' φ hφc hφs R)
    (fun u g => R1CentreAbsorb.Ffun_centralScalar_mul K L D σ hgen νZL ΩL hΩL ξ' hξt' R φ u (hone u) g)
    X Ω₁ Ω₂ hΩ₁

end Solution

end S_AutomorphicForm_TwistedBruhat_lintegral_iwasawa_indicator_tsum_tsum_enorm_sub_eq_measure_mul_lintegral_of_sigmaInvariant
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_lintegral_iwasawa_indicator_tsum_tsum_enorm_sub_eq_measure_mul_lintegral_of_sigmaInvariant (solution)
