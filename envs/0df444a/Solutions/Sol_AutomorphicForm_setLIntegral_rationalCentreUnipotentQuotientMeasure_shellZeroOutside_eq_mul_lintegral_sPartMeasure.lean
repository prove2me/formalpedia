-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a50bfd24-73c6-58d1-b1da-82bfa0eac079

import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_IwasawaShellIndex
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent
import Theorems.Thm_AutomorphicForm_isLocallyConstant_iwasawaShellIndex_and_measurable
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure.AutomorphicForm IsDedekindDomain Topology"
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "RankinSelberg.shellZeroOutside rationalCentreUnipotent RationalCentreUnipotentQuotient rationalCentreUnipotentQuotientMeasure AdelicGL2 centralScalar adelicMaximalCompact mem_adelicMaximalCompact_iff valued_finComponent_apply_le_one valued_det_finComponent_eq_one maximalCompactHaar WindowedSiegel.isRowIsometry_one iwasawaShellIndex localMatrix localMatrix_apply localMatrix_mul iwasawaShellIndex_eq_zero_iff' iwasawaShellIndex_eq iwasawaShellIndex_eq_of_localMatrix iwasawaShellIndex_centralScalar_mul iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent isLocallyConstant_iwasawaShellIndex_and_measurable"
p2m_open "AutomorphicForm"

namespace SPart

variable (K : Type) [Field K] [NumberField K]

scoped instance : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

scoped instance secondCountableTopology_maxCpt : SecondCountableTopology (adelicMaximalCompact K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

scoped instance : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K

scoped instance secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem continuous_diagOne :
    Continuous (diagOne : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K) := by
  have hval : Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
      ((diagOne u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    change Continuous fun u : (AdeleRing (𝓞 K) K)ˣ => Matrix.diagonal ![(u : AdeleRing (𝓞 K) K), 1]
    refine (continuous_pi fun i => ?_).matrix_diagonal
    fin_cases i
    · exact Units.continuous_val
    · exact continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp_rw [← map_inv]
  exact hval.comp continuous_inv

theorem shellZeroOutside_eq (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RankinSelberg.shellZeroOutside K S = {g | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → iwasawaShellIndex K v g = 0} := by
  ext g
  simp only [RankinSelberg.shellZeroOutside, Set.mem_setOf_eq]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [iwasawaShellIndex_eq_zero_iff']

theorem isClosed_shellZeroOutside (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsClosed (RankinSelberg.shellZeroOutside K S) := by
  rw [shellZeroOutside_eq]
  have : {g : AdelicGL2 (𝓞 K) K | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → iwasawaShellIndex K v g = 0} =
      ⋂ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S), iwasawaShellIndex K v ⁻¹' {0} := by
    ext g; simp
  rw [this]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    (AutomorphicForm.isLocallyConstant_iwasawaShellIndex_and_measurable K v).1.isClosed_fiber 0

theorem measurableSet_shellZeroOutside (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MeasurableSet (RankinSelberg.shellZeroOutside K S) :=
  (isClosed_shellZeroOutside K S).measurableSet

theorem mul_mem_shellZeroOutside_iff (S : Finset (HeightOneSpectrum (𝓞 K))) {x : AdelicGL2 (𝓞 K) K}
    (hx : x ∈ rationalCentreUnipotent K) (g : AdelicGL2 (𝓞 K) K) :
    x * g ∈ RankinSelberg.shellZeroOutside K S ↔ g ∈ RankinSelberg.shellZeroOutside K S := by
  simp only [shellZeroOutside_eq, Set.mem_setOf_eq,
    AutomorphicForm.iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent K _ x hx]

theorem localMatrix_diagOne (v : HeightOneSpectrum (𝓞 K)) (t : (AdeleRing (𝓞 K) K)ˣ) :
    localMatrix v (diagOne t : AdelicGL2 (𝓞 K) K) = Matrix.diagonal ![((t : AdeleRing (𝓞 K) K)).2 v, 1] := by
  ext i j
  rw [localMatrix_apply, diagOne_coe_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

theorem iwasawaShellIndex_eq_zero_of_mem (v : HeightOneSpectrum (𝓞 K)) {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ adelicMaximalCompact K) : iwasawaShellIndex K v k = 0 := by

  have hle : ∀ i j, Valued.v (localMatrix v k i j) ≤ 1 := fun i j => by
    rw [localMatrix_apply, ← glFin_apply, ← finComponent_apply]
    exact (valued_finComponent_apply_le_one hk v i j).1
  have hdet : Valued.v (localMatrix v k).det = 1 := by
    have h := valued_det_finComponent_eq_one hk v
    have : (finComponent (𝓞 K) K v (glFin (𝓞 K) K k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = localMatrix v k := by
      ext i j; rw [finComponent_apply, glFin_apply, localMatrix_apply]
    rwa [this] at h

  have hmax : max (Valued.v (localMatrix v k 1 0)) (Valued.v (localMatrix v k 1 1)) = 1 := by
    apply le_antisymm (max_le (hle 1 0) (hle 1 1))
    by_contra hlt
    rw [not_le] at hlt
    have h10 : Valued.v (localMatrix v k 1 0) < 1 := lt_of_le_of_lt (le_max_left _ _) hlt
    have h11 : Valued.v (localMatrix v k 1 1) < 1 := lt_of_le_of_lt (le_max_right _ _) hlt
    have : Valued.v (localMatrix v k).det < 1 := by
      rw [Matrix.det_fin_two]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
      · rw [Valuation.map_mul]
        calc Valued.v (localMatrix v k 0 0) * Valued.v (localMatrix v k 1 1)
            ≤ 1 * Valued.v (localMatrix v k 1 1) := mul_le_mul' (hle 0 0) le_rfl
          _ < 1 := by rw [one_mul]; exact h11
      · rw [Valuation.map_mul]
        calc Valued.v (localMatrix v k 0 1) * Valued.v (localMatrix v k 1 0)
            ≤ 1 * Valued.v (localMatrix v k 1 0) := mul_le_mul' (hle 0 1) le_rfl
          _ < 1 := by rw [one_mul]; exact h10
    rw [hdet] at this
    exact lt_irrefl _ this
  rw [iwasawaShellIndex_eq, hmax, hdet, WithZero.log_one]
  simp

theorem iwasawaShellIndex_centralScalar_diagOne_mul_eq_zero_iff (v : HeightOneSpectrum (𝓞 K))
    (z t : (AdeleRing (𝓞 K) K)ˣ) {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K) :
    iwasawaShellIndex K v (centralScalar (𝓞 K) K z * diagOne t * k) = 0 ↔ Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = 1 := by
  have ht0 : ((t : AdeleRing (𝓞 K) K)).2 v ≠ 0 := by
    intro h0
    have := NumberField.Idele.valued_snd_ne_zero K v t
    rw [h0, Valuation.map_zero] at this
    exact this rfl
  rw [mul_assoc, iwasawaShellIndex_centralScalar_mul]
  have hrel := iwasawaShellIndex_eq_of_localMatrix v k (diagOne t * k) (((t : AdeleRing (𝓞 K) K)).2 v) ht0
    (fun j => by rw [localMatrix_mul, localMatrix_diagOne, Matrix.diagonal_mul]; simp)
    (by rw [localMatrix_mul, localMatrix_diagOne, Matrix.det_mul, Matrix.det_diagonal]; simp)
  rw [hrel, iwasawaShellIndex_eq_zero_of_mem K v hk, zero_sub, neg_eq_zero]
  have hne : (Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ht0
  constructor
  · intro h
    rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
  · intro h; rw [h, WithZero.log_one]

theorem centralScalar_diagOne_mul_mem_shellZeroOutside_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z t : (AdeleRing (𝓞 K) K)ˣ) {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K) :
    centralScalar (𝓞 K) K z * diagOne t * k ∈ RankinSelberg.shellZeroOutside K S ↔
      t ∈ (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 K) K)ˣ) := by
  rw [shellZeroOutside_eq, Set.mem_setOf_eq, SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  refine forall_congr' fun v => ?_
  rw [Finset.mem_coe]
  refine imp_congr_right fun _ => ?_
  rw [iwasawaShellIndex_centralScalar_diagOne_mul_eq_zero_iff K v z t hk,
    IsDedekindDomain.FiniteAdeleRing.integer_and_inv_integer_iff_valuation_eq_one]
  rfl

theorem diagOne_mem_adelicMaximalCompact {u : (AdeleRing (𝓞 K) K)ˣ} (harch : (u : AdeleRing (𝓞 K) K).1 = 1)
    (hfin : NumberField.AdeleRing.finitePartUnits (𝓞 K) K u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K) :
    (diagOne u : AdelicGL2 (𝓞 K) K) ∈ adelicMaximalCompact K := by
  rw [mem_adelicMaximalCompact_iff]
  obtain ⟨h1, h2⟩ := hfin
  have hinv : ∀ v, ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K := fun v => by
    have := h2 v
    rwa [← map_inv] at this
  have hval : ∀ v, ((u : AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K := fun v => h1 v
  constructor
  · rw [mem_finiteIntegralGL2_iff]
    constructor
    · intro i j v
      rw [glFin_apply, diagOne_coe_apply]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq]
        fin_cases i
        · exact hval v
        · exact one_mem _
      · rw [Matrix.diagonal_apply_ne _ hij]; exact zero_mem _
    · intro i j v
      rw [← map_inv, ← map_inv, glFin_apply, diagOne_coe_apply]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq]
        fin_cases i
        · exact hinv v
        · exact one_mem _
      · rw [Matrix.diagonal_apply_ne _ hij]; exact zero_mem _
  · intro w
    have : archComponent K w (glArch (𝓞 K) K (diagOne u)) = 1 := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      rw [archComponent_apply, glArch_apply, diagOne_coe_apply, Matrix.diagonal_apply]
      change _ = (1 : Matrix (Fin 2) (Fin 2) w.Completion) i j
      rw [Matrix.one_apply]
      split_ifs with h
      · subst h; fin_cases i
        · change ((u : AdeleRing (𝓞 K) K)).1 w = 1; rw [harch]; rfl
        · rfl
      · rfl
    rw [this]; exact WindowedSiegel.isRowIsometry_one

theorem diagOne_unitPart_mem (S : Finset (HeightOneSpectrum (𝓞 K))) (t : (AdeleRing (𝓞 K) K)ˣ) :
    (diagOne (NumberField.Idele.unitPart K S t) : AdelicGL2 (𝓞 K) K) ∈ adelicMaximalCompact K :=
  diagOne_mem_adelicMaximalCompact K (NumberField.Idele.unitPart_fst K S t)
    (NumberField.Idele.finitePartUnits_unitPart_mem_unitIdeles K S t)

theorem ideleNorm_unitPart (S : Finset (HeightOneSpectrum (𝓞 K))) (t : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm K (NumberField.Idele.unitPart K S t) = 1 :=
  NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K _
    (NumberField.Idele.unitPart_fst K S t) (NumberField.Idele.finitePartUnits_unitPart_mem_unitIdeles K S t)

theorem eq_partAt_mul_unitPart (S : Finset (HeightOneSpectrum (𝓞 K))) {t : (AdeleRing (𝓞 K) K)ˣ}
    (ht : t ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K)))) :
    t = NumberField.Idele.partAt K S t * NumberField.Idele.unitPart K S t := by
  have ht' : t ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S ∪ {v | v ∈ ([] : List (HeightOneSpectrum (𝓞 K)))}) := by
    simpa using ht
  have h := NumberField.Idele.eq_partAt_mul_prod_mul_unitPart K S [] (by simp) List.nodup_nil t ht'
  simpa using h

theorem ideleNorm_eq_of_mem (S : Finset (HeightOneSpectrum (𝓞 K))) {t : (AdeleRing (𝓞 K) K)ˣ}
    (ht : t ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K)))) :
    NumberField.TateGlobal.ideleNorm K t = NumberField.TateGlobal.ideleNorm K (NumberField.Idele.partAt K S t) := by
  conv_lhs => rw [eq_partAt_mul_unitPart K S ht]
  unfold NumberField.TateGlobal.ideleNorm
  rw [map_mul, NNReal.coe_mul]
  have h1 := ideleNorm_unitPart K S t
  unfold NumberField.TateGlobal.ideleNorm at h1
  rw [h1, mul_one]

theorem main (c : ℝ≥0∞)
    (hc : ∀ (D : Set (AdeleRing (𝓞 K) K)ˣ), MeasurableSet D →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) →
      ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
        (∀ x ∈ rationalCentreUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalCentreUnipotentQuotientMeasure K) =
          c * ∫⁻ z in D, ∫⁻ t, ∫⁻ k,
                f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f)
    (hfH : ∀ x ∈ rationalCentreUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) :
    ∫⁻ q in {q : RationalCentreUnipotentQuotient K | q.out ∈ RankinSelberg.shellZeroOutside K S}, f q.out
        ∂(rationalCentreUnipotentQuotientMeasure K) =
      c * ∫⁻ z in D, ∫⁻ t, ∫⁻ k,
            f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S) ∂(NumberField.Idele.idelicHaar K) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  set Z := RankinSelberg.shellZeroOutside K S with hZ
  have hZm : MeasurableSet Z := measurableSet_shellZeroOutside K S

  set A : Set (RationalCentreUnipotentQuotient K) := {q | q.out ∈ Z} with hA
  have hAeq : (Quotient.mk'' : AdelicGL2 (𝓞 K) K → RationalCentreUnipotentQuotient K) ⁻¹' A = Z := by
    ext g
    simp only [hA, Set.mem_preimage, Set.mem_setOf_eq]
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (@Quotient.mk_out _ (MulAction.orbitRel (rationalCentreUnipotent K) (AdelicGL2 (𝓞 K) K)) g))
    rw [show (Quotient.mk'' g : RationalCentreUnipotentQuotient K).out = (x : AdelicGL2 (𝓞 K) K) * g from hx.symm]
    exact mul_mem_shellZeroOutside_iff K S x.2 g
  have hAm : MeasurableSet A := measurableSet_quotient.mpr (by rw [hAeq]; exact hZm)
  rw [← lintegral_indicator hAm]
  have hind : ∀ q : RationalCentreUnipotentQuotient K, A.indicator (fun q => f q.out) q = Z.indicator f q.out := fun q => by
    by_cases hq : q.out ∈ Z
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show q ∈ A from hq)]
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (show q ∉ A from hq)]
  simp_rw [hind]

  have hF : Measurable (Z.indicator f) := hf.indicator hZm
  have hFH : ∀ x ∈ rationalCentreUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, Z.indicator f (x * g) = Z.indicator f g := by
    intro x hx g
    by_cases hg : g ∈ Z
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((mul_mem_shellZeroOutside_iff K S hx g).mpr hg), hfH x hx]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((mul_mem_shellZeroOutside_iff K S hx g).mp h))]
  rw [hc D hD hDF (Z.indicator f) hF hFH]
  congr 1
  refine setLIntegral_congr_fun hD (fun z _ => ?_)

  set U : Set (AdeleRing (𝓞 K) K)ˣ :=
    (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 K) K)ˣ) with hU_def
  have hU : MeasurableSet U := (NumberField.Idele.isOpen_unitIdelesOutside K _).measurableSet
  set G' : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞ := fun t => ∫⁻ k, f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
    ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) ∂(maximalCompactHaar K) with hG'_def
  have hG' : Measurable G' := by
    refine Measurable.lintegral_prod_right' (f := fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
      f (centralScalar (𝓞 K) K z * diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K p.1)⁻¹)) ?_
    refine (hf.comp ?_).mul ?_
    · exact ((continuous_const.mul ((continuous_diagOne K).comp continuous_fst)).mul
        (continuous_subtype_val.comp continuous_snd)).measurable
    · exact ENNReal.measurable_ofReal.comp (((NumberField.TateGlobal.continuous_ideleNorm K).measurable.comp measurable_fst).inv)
  have h3 : ∀ t, ∫⁻ k, Z.indicator f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
      ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) ∂(maximalCompactHaar K) = U.indicator G' t := by
    intro t
    by_cases ht : t ∈ U
    · rw [Set.indicator_of_mem ht]
      refine lintegral_congr fun k => ?_
      rw [Set.indicator_of_mem ((centralScalar_diagOne_mul_mem_shellZeroOutside_iff K S z t k.2).mpr ht)]
    · rw [Set.indicator_of_notMem ht]
      have : ∀ k : adelicMaximalCompact K, Z.indicator f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) = 0 := fun k => by
        rw [Set.indicator_of_notMem (fun h => ht ((centralScalar_diagOne_mul_mem_shellZeroOutside_iff K S z t k.2).mp h)),
          zero_mul]
      simp_rw [this, lintegral_zero]
  simp_rw [h3]
  rw [lintegral_indicator hU]

  have h4 : ∀ t ∈ U, G' t = G' (NumberField.Idele.partAt K S t) := by
    intro t ht
    simp only [hG'_def]
    rw [← ideleNorm_eq_of_mem K S ht]
    have hsplit : diagOne t = diagOne (NumberField.Idele.partAt K S t) * diagOne (NumberField.Idele.unitPart K S t) := by
      conv_lhs => rw [eq_partAt_mul_unitPart K S ht]
      rw [map_mul]
    set k₀ : adelicMaximalCompact K := ⟨diagOne (NumberField.Idele.unitPart K S t), diagOne_unitPart_mem K S t⟩ with hk₀
    have := lintegral_mul_left_eq_self (μ := maximalCompactHaar K)
      (fun k : adelicMaximalCompact K => f (centralScalar (𝓞 K) K z * diagOne (NumberField.Idele.partAt K S t) *
        (k : AdelicGL2 (𝓞 K) K)) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)) k₀
    rw [← this]
    refine lintegral_congr fun k => ?_
    simp only [hsplit, hk₀, Subgroup.coe_mul, mul_assoc]
  rw [setLIntegral_congr_fun hU h4, NumberField.Idele.sPartMeasure, lintegral_map hG' (NumberField.Idele.measurable_partAt K S)]

end SPart
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure.AutomorphicForm.SPart"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure.AutomorphicForm.SPart P2MW.S_AutomorphicForm_setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure.AutomorphicForm.SPart P2MW.S_AutomorphicForm_setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure.AutomorphicForm"

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c : ℝ≥0∞)
    (hc : ∀ (D : Set (NumberField.AdeleRing (𝓞 K) K)ˣ), MeasurableSet D →
        MeasureTheory.IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) →
      ∀ f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
        (∀ x ∈ AutomorphicForm.rationalCentreUnipotent K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(AutomorphicForm.rationalCentreUnipotentQuotientMeasure K) =
          c * ∫⁻ z in D, ∫⁻ t, ∫⁻ k,
                f (AutomorphicForm.centralScalar (𝓞 K) K z * NumberField.AdelicLevel.diagOne t * (k : AutomorphicForm.AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(AutomorphicForm.maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (D : Set (NumberField.AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : MeasureTheory.IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f)
    (hfH : ∀ x ∈ AutomorphicForm.rationalCentreUnipotent K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K, f (x * g) = f g) :
    ∫⁻ q in {q : AutomorphicForm.RationalCentreUnipotentQuotient K | q.out ∈ AutomorphicForm.RankinSelberg.shellZeroOutside K S}, f q.out
        ∂(AutomorphicForm.rationalCentreUnipotentQuotientMeasure K) =
      c * ∫⁻ z in D, ∫⁻ t, ∫⁻ k,
            f (AutomorphicForm.centralScalar (𝓞 K) K z * NumberField.AdelicLevel.diagOne t * (k : AutomorphicForm.AdelicGL2 (𝓞 K) K)) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
          ∂(AutomorphicForm.maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S) ∂(NumberField.Idele.idelicHaar K) :=
  AutomorphicForm.SPart.main K c hc S D hD hDF f hf hfH

end S_AutomorphicForm_setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure (solution)
