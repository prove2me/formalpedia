-- Prove2me | solution 1 for AutomorphicForm.exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f08fcd84-a24b-5b58-bc72-2457214d7049

import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_AutomorphicForm_isClosed_rationalCentreUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.AutomorphicForm Topology"
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalCentreUnipotent RationalCentreUnipotentQuotient rationalCentreUnipotentHaar rationalCentreUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar unipotentGL2 unipotentGL2_coe AdelicGL2 globalPoints centralScalar adelicMaximalCompact maximalCompactHaar isClosed_rationalCentreUnipotent isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant"
p2m_open "AutomorphicForm"

namespace IwasawaQuot

variable (K : Type) [Field K] [NumberField K]

scoped instance : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

scoped instance : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K

scoped instance secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompactSpace_idele : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance sigmaCompactSpace_idele : SigmaCompactSpace (AdeleRing (𝓞 K) K)ˣ :=
  @sigmaCompactSpace_of_locallyCompact_secondCountable _ _ (locallyCompactSpace_idele K) (secondCountableTopology_idele K)

scoped instance secondCountableTopology_maxCpt : SecondCountableTopology (adelicMaximalCompact K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

scoped instance sigmaFinite_adelicAddHaar : SigmaFinite (adelicAddHaar (𝓞 K) K) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K; infer_instance

scoped instance sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar K) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K; infer_instance

scoped instance sigmaFinite_maximalCompactHaar : SigmaFinite (maximalCompactHaar K) := inferInstance

scoped instance sFinite_adelicGLHaar : SFinite (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K; infer_instance

theorem measurable_density :
    Measurable (HaarQuotient.density (rationalCentreUnipotent K) (rationalCentreUnipotentHaar K)) := by
  have hH := AutomorphicForm.isClosed_rationalCentreUnipotent K
  haveI := (AutomorphicForm.isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant K).1
  haveI : SecondCountableTopology (rationalCentreUnipotent K) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (rationalCentreUnipotent K) := hH.locallyCompactSpace
  haveI : SigmaCompactSpace (rationalCentreUnipotent K) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hw : Measurable (HaarQuotient.weight (rationalCentreUnipotent K) (rationalCentreUnipotentHaar K)) := by
    unfold HaarQuotient.weight
    split_ifs with h
    · exact Measurable.ennreal_tsum fun n =>
        (measurable_const.mul (measurable_const.indicator isOpen_interior.measurableSet))
    · exact measurable_zero
  have h2 : Measurable fun g : AdelicGL2 (𝓞 K) K =>
      ∫⁻ x : rationalCentreUnipotent K, HaarQuotient.weight (rationalCentreUnipotent K) (rationalCentreUnipotentHaar K)
        ((x : AdelicGL2 (𝓞 K) K) * g) ∂(rationalCentreUnipotentHaar K) := by
    refine Measurable.lintegral_prod_right ?_
    exact hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.mul h2.inv

theorem lintegral_quotient_eq_lintegral_mul_density (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f)
    (hfH : ∀ x ∈ rationalCentreUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) :
    ∫⁻ q, f q.out ∂(rationalCentreUnipotentQuotientMeasure K) =
      ∫⁻ g, f g * HaarQuotient.density (rationalCentreUnipotent K) (rationalCentreUnipotentHaar K) g
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have hH := AutomorphicForm.isClosed_rationalCentreUnipotent K
  haveI := (AutomorphicForm.isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant K).1
  haveI := (AutomorphicForm.isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant K).2
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set ρ := HaarQuotient.density (rationalCentreUnipotent K) (rationalCentreUnipotentHaar K) with hρ
  have hρm : Measurable ρ := measurable_density K
  have hsec : ∀ g : AdelicGL2 (𝓞 K) K, ∫⁻ x : rationalCentreUnipotent K, ρ ((x : AdelicGL2 (𝓞 K) K) * g)
      ∂(rationalCentreUnipotentHaar K) = 1 :=
    HaarQuotient.lintegral_density_mul_eq_one (rationalCentreUnipotent K) hH (rationalCentreUnipotentHaar K)
  have h1 : ∀ q : RationalCentreUnipotentQuotient K,
      f q.out = ∫⁻ x : rationalCentreUnipotent K, f ((x : AdelicGL2 (𝓞 K) K) * q.out) * ρ ((x : AdelicGL2 (𝓞 K) K) * q.out)
        ∂(rationalCentreUnipotentHaar K) := by
    intro q
    simp_rw [hfH _ (Subtype.mem _)]
    have hm : Measurable fun x : rationalCentreUnipotent K => ρ ((x : AdelicGL2 (𝓞 K) K) * q.out) :=
      hρm.comp (continuous_subtype_val.mul continuous_const).measurable
    rw [lintegral_const_mul _ hm, hsec, mul_one]
  rw [rationalCentreUnipotentQuotientMeasure]
  simp_rw [h1]
  exact (HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out (adelicGLHaar (Fin 2) (𝓞 K) K) (rationalCentreUnipotent K)
    hH (rationalCentreUnipotentHaar K) (fun g => f g * ρ g) (hf.mul hρm)).symm

theorem continuous_unipotentGL2 :
    Continuous (fun y : AdeleRing (𝓞 K) K => (unipotentGL2 y : AdelicGL2 (𝓞 K) K)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Function.comp_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : ∀ y : AdeleRing (𝓞 K) K, (↑((unipotentGL2 y : AdelicGL2 (𝓞 K) K)⁻¹) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = !![1, -y; 0, 1] := fun y => rfl
    simp_rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 K) K : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K) := by
  have hval : Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
      ((centralScalar (𝓞 K) K u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    change Continuous fun u : (AdeleRing (𝓞 K) K)ˣ => Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K)
    simp_rw [Matrix.scalar_apply]
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp_rw [← map_inv]
  exact hval.comp continuous_inv

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

abbrev P := ((AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ) × (AdeleRing (𝓞 K) K)ˣ) × adelicMaximalCompact K

def coord (p : P K) : AdelicGL2 (𝓞 K) K :=
  unipotentGL2 p.1.1.1 * centralScalar (𝓞 K) K p.1.1.2 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 K) K)

theorem continuous_coord : Continuous (coord K) := by
  unfold coord
  exact ((((continuous_unipotentGL2 K).comp (continuous_fst.comp (continuous_fst.comp continuous_fst))).mul
    ((continuous_centralScalar K).comp (continuous_snd.comp (continuous_fst.comp continuous_fst)))).mul
    ((continuous_diagOne K).comp (continuous_snd.comp continuous_fst))).mul (continuous_subtype_val.comp continuous_snd)

def wt (t : (AdeleRing (𝓞 K) K)ˣ) : ℝ≥0∞ := ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)

theorem countable_numberField : Countable K := by
  let b := Module.finBasis ℚ K
  refine Function.Surjective.countable (f := fun c : Fin (Module.finrank ℚ K) → ℚ => ∑ i, c i • b i) fun x => ?_
  exact ⟨fun i => b.repr x i, b.sum_repr x⟩

scoped instance countable_principalIdeles : Countable (M4aHerbrand.principalIdeles (𝓞 K) K) := by
  haveI := countable_numberField K
  haveI : Countable Kˣ := Function.Injective.countable (f := (Units.val : Kˣ → K)) Units.val_injective
  change Countable ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range : Set (AdeleRing (𝓞 K) K)ˣ)
  rw [MonoidHom.coe_range]
  exact (Set.countable_range _).to_subtype

abbrev ratCentral (a : Kˣ) : AdelicGL2 (𝓞 K) K :=
  globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)

theorem ratCentral_eq_centralScalar (a : Kˣ) :
    ratCentral K a = centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (a : K)) i j) =
    (Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem ratCentral_mem (a : Kˣ) : ratCentral K a ∈ rationalCentreUnipotent K :=
  Subgroup.mem_sup_left ⟨a, rfl⟩

theorem unipotentGL2_mem (x : AdeleRing (𝓞 K) K) : (unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈ rationalCentreUnipotent K :=
  Subgroup.mem_sup_right ⟨Multiplicative.ofAdd x, rfl⟩

theorem centralScalar_mul_comm (u : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K u * g = g * centralScalar (𝓞 K) K u := by
  refine Units.ext ?_
  change Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K)
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

theorem ratCentral_mul_unipotentGL2_mem (a : Kˣ) (y : AdeleRing (𝓞 K) K) :
    ratCentral K a * unipotentGL2 y ∈ rationalCentreUnipotent K :=
  Subgroup.mul_mem_sup ⟨a, rfl⟩ ⟨Multiplicative.ofAdd y, rfl⟩

theorem lintegral_rationalCentreUnipotentHaar (G : rationalCentreUnipotent K → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂(rationalCentreUnipotentHaar K) =
      ∑' a : Kˣ, ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ *
        ∫⁻ y, G ⟨ratCentral K a * unipotentGL2 y, ratCentral_mul_unipotentGL2_mem K a y⟩ ∂(adelicAddHaar (𝓞 K) K) := by
  rw [rationalCentreUnipotentHaar, lintegral_sum_measure]
  refine tsum_congr fun a => ?_
  have hι : Measurable (fun n : adelicUnipotent K =>
      (⟨ratCentral K a * (n : AdelicGL2 (𝓞 K) K), Subgroup.mul_mem_sup ⟨a, rfl⟩ n.2⟩ : rationalCentreUnipotent K)) :=
    ((continuous_const.mul continuous_subtype_val).measurable).subtype_mk
  rw [lintegral_map hG hι, unipotentHaar]
  have hto : Measurable (toAdelicUnipotent K) := by
    refine (Continuous.subtype_mk ?_ _).measurable
    exact (continuous_unipotentGL2 K)
  have hGι : Measurable (fun n : adelicUnipotent K =>
      G ⟨ratCentral K a * (n : AdelicGL2 (𝓞 K) K), Subgroup.mul_mem_sup ⟨a, rfl⟩ n.2⟩) := hG.comp hι
  rw [lintegral_map hGι hto, lintegral_smul_measure, smul_eq_mul]
  rfl

theorem tsum_lintegral_density (g : AdelicGL2 (𝓞 K) K) :
    ∑' ζ : M4aHerbrand.principalIdeles (𝓞 K) K,
        ∫⁻ x, HaarQuotient.density (rationalCentreUnipotent K) (rationalCentreUnipotentHaar K)
          (unipotentGL2 x * (centralScalar (𝓞 K) K ((ζ⁻¹ : M4aHerbrand.principalIdeles (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ) * g))
          ∂(adelicAddHaar (𝓞 K) K) =
      (adelicAddHaar (𝓞 K) K) (adelicBox K) := by
  have hH := AutomorphicForm.isClosed_rationalCentreUnipotent K
  haveI := (AutomorphicForm.isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant K).1
  haveI := (AutomorphicForm.isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant K).2
  set ρ := HaarQuotient.density (rationalCentreUnipotent K) (rationalCentreUnipotentHaar K) with hρ
  have hρm : Measurable ρ := measurable_density K

  have hinj : Function.Injective (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) := by
    intro a b h
    have h' := congrArg Units.val h
    simp only [Units.coe_map, MonoidHom.coe_coe] at h'
    exact Units.ext (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K) h')
  set e : Kˣ ≃ M4aHerbrand.principalIdeles (𝓞 K) K := (MonoidHom.ofInjective hinj).toEquiv with he
  have he' : ∀ a : Kˣ, ((e a : M4aHerbrand.principalIdeles (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a := fun a => rfl
  set T : M4aHerbrand.principalIdeles (𝓞 K) K → ℝ≥0∞ := fun ζ =>
    ∫⁻ x, ρ (unipotentGL2 x * (centralScalar (𝓞 K) K ((ζ : M4aHerbrand.principalIdeles (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ) * g))
      ∂(adelicAddHaar (𝓞 K) K) with hT
  calc ∑' ζ : M4aHerbrand.principalIdeles (𝓞 K) K, T ζ⁻¹
      = ∑' ζ : M4aHerbrand.principalIdeles (𝓞 K) K, T ζ := (Equiv.inv _).tsum_eq T
    _ = ∑' a : Kˣ, T (e a) := (e.tsum_eq T).symm
    _ = ∑' a : Kˣ, ∫⁻ x, ρ ((ratCentral K a * unipotentGL2 x) * g) ∂(adelicAddHaar (𝓞 K) K) := by
        refine tsum_congr fun a => ?_
        simp only [hT, he', ← ratCentral_eq_centralScalar]
        refine lintegral_congr fun x => ?_
        rw [← mul_assoc, show unipotentGL2 x * ratCentral K a = ratCentral K a * unipotentGL2 x from by
          rw [ratCentral_eq_centralScalar, centralScalar_mul_comm]]
    _ = (adelicAddHaar (𝓞 K) K) (adelicBox K) := by
        have hbox0 := (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos K).ne'
        have hboxtop := (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top K).ne
        have hsum := lintegral_rationalCentreUnipotentHaar K (fun h => ρ ((h : AdelicGL2 (𝓞 K) K) * g))
          (hρm.comp (continuous_subtype_val.mul continuous_const).measurable)
        rw [HaarQuotient.lintegral_density_mul_eq_one (rationalCentreUnipotent K) hH (rationalCentreUnipotentHaar K) g,
          ENNReal.tsum_mul_left] at hsum

        have : ∑' a : Kˣ, ∫⁻ y, ρ ((ratCentral K a * unipotentGL2 y) * g) ∂(adelicAddHaar (𝓞 K) K) =
            (adelicAddHaar (𝓞 K) K) (adelicBox K) := by
          have h3 := congrArg (fun r => (adelicAddHaar (𝓞 K) K) (adelicBox K) * r) hsum
          simp only [mul_one, ← mul_assoc, ENNReal.mul_inv_cancel hbox0 hboxtop, one_mul] at h3
          exact h3.symm
        exact this

theorem swap4 (F : P K → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k, F (((x, u), t), k) ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K)
        ∂(NumberField.Idele.idelicHaar K) ∂(adelicAddHaar (𝓞 K) K) =
      ∫⁻ u, ∫⁻ t, ∫⁻ k, ∫⁻ x, F (((x, u), t), k) ∂(adelicAddHaar (𝓞 K) K) ∂(maximalCompactHaar K)
        ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
  have h3 : Measurable fun q : (AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ) × (AdeleRing (𝓞 K) K)ˣ =>
      ∫⁻ k, F (q, k) ∂(maximalCompactHaar K) := hF.lintegral_prod_right'
  have h2 : Measurable fun r : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ =>
      ∫⁻ t, ∫⁻ k, F ((r, t), k) ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) := h3.lintegral_prod_right'
  rw [lintegral_lintegral_swap h2.aemeasurable]
  refine lintegral_congr fun u => ?_
  have h3u : Measurable fun r : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ =>
      ∫⁻ k, F (((r.1, u), r.2), k) ∂(maximalCompactHaar K) :=
    h3.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  rw [lintegral_lintegral_swap h3u.aemeasurable]
  refine lintegral_congr fun t => ?_
  have hFut : Measurable fun r : AdeleRing (𝓞 K) K × adelicMaximalCompact K => F (((r.1, u), t), r.2) :=
    hF.comp (((measurable_fst.prodMk measurable_const).prodMk measurable_const).prodMk measurable_snd)
  rw [lintegral_lintegral_swap hFut.aemeasurable]

def coord3 (q : ((AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) × adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K :=
  centralScalar (𝓞 K) K q.1.1 * diagOne q.1.2 * (q.2 : AdelicGL2 (𝓞 K) K)

theorem continuous_coord3 : Continuous (coord3 K) := by
  unfold coord3
  exact (((continuous_centralScalar K).comp (continuous_fst.comp continuous_fst)).mul
    ((continuous_diagOne K).comp (continuous_snd.comp continuous_fst))).mul (continuous_subtype_val.comp continuous_snd)

theorem measurable_wt : Measurable (wt K) := by
  unfold wt
  exact ENNReal.measurable_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm K).measurable.inv)

def R (g : AdelicGL2 (𝓞 K) K) : ℝ≥0∞ :=
  ∫⁻ x, HaarQuotient.density (rationalCentreUnipotent K) (rationalCentreUnipotentHaar K) (unipotentGL2 x * g)
    ∂(adelicAddHaar (𝓞 K) K)

theorem measurable_R : Measurable (R K) := by
  unfold R
  refine Measurable.lintegral_prod_right ?_
  exact (measurable_density K).comp (((continuous_unipotentGL2 K).comp continuous_snd).mul continuous_fst).measurable

theorem main :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ (D : Set (AdeleRing (𝓞 K) K)ˣ), MeasurableSet D →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) →
      ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
        (∀ x ∈ rationalCentreUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalCentreUnipotentQuotientMeasure K) =
          c * ∫⁻ z in D, ∫⁻ t, ∫⁻ k,
                f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  set ρ := HaarQuotient.density (rationalCentreUnipotent K) (rationalCentreUnipotentHaar K) with hρ
  have hρm : Measurable ρ := measurable_density K
  have hbox0 := (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos K).ne'
  have hboxtop := (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top K).ne
  obtain ⟨c₁, hc₁0, hc₁top, hPKB⟩ := NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa K
  refine ⟨c₁ * (adelicAddHaar (𝓞 K) K) (adelicBox K), mul_ne_zero hc₁0 hbox0, ENNReal.mul_ne_top hc₁top hboxtop,
    fun D hD hFD f hf hfH => ?_⟩
  rw [lintegral_quotient_eq_lintegral_mul_density K f hf hfH, ← hρ, hPKB (fun g => f g * ρ g) (hf.mul hρm),
    mul_assoc]
  beta_reduce
  congr 1

  set F : P K → ℝ≥0∞ := fun p => f (coord K p) * ρ (coord K p) * wt K p.1.2 with hF_def
  have hF : Measurable F :=
    ((hf.comp (continuous_coord K).measurable).mul (hρm.comp (continuous_coord K).measurable)).mul
      ((measurable_wt K).comp (measurable_snd.comp measurable_fst))

  have hA := swap4 K F hF
  simp only [hF_def, coord, wt] at hA
  rw [hA]

  have hB : ∀ (u t : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
      ∫⁻ x, f (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
          ρ (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) ∂(adelicAddHaar (𝓞 K) K) =
        f (coord3 K ((u, t), k)) * wt K t * R K (coord3 K ((u, t), k)) := by
    intro u t k
    have hx : ∀ x, unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K) =
        unipotentGL2 x * coord3 K ((u, t), k) := fun x => by simp only [coord3, mul_assoc]
    simp_rw [hx, hfH _ (unipotentGL2_mem K _)]
    have hm : Measurable fun x : AdeleRing (𝓞 K) K => ρ (unipotentGL2 x * coord3 K ((u, t), k)) :=
      hρm.comp ((continuous_unipotentGL2 K).mul continuous_const).measurable
    have : ∀ x, f (coord3 K ((u, t), k)) * ρ (unipotentGL2 x * coord3 K ((u, t), k)) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹) =
        (f (coord3 K ((u, t), k)) * wt K t) * ρ (unipotentGL2 x * coord3 K ((u, t), k)) := fun x => by
      simp only [wt]; ring
    simp_rw [this]
    rw [lintegral_const_mul _ hm]
    rfl
  simp_rw [hB]

  haveI : MeasurableConstSMul (M4aHerbrand.principalIdeles (𝓞 K) K) (AdeleRing (𝓞 K) K)ˣ :=
    ⟨fun ζ => measurable_const_mul ((ζ : M4aHerbrand.principalIdeles (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ)⟩
  haveI : SMulInvariantMeasure (M4aHerbrand.principalIdeles (𝓞 K) K) (AdeleRing (𝓞 K) K)ˣ (NumberField.Idele.idelicHaar K) :=
    inferInstance

  set Ψ : AdelicGL2 (𝓞 K) K → ((AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) × adelicMaximalCompact K → ℝ≥0∞ :=
    fun c q => f (coord3 K q) * wt K q.1.2 * R K (c * coord3 K q) with hΨ_def
  have hΨ : ∀ c, Measurable (Ψ c) := fun c =>
    ((hf.comp (continuous_coord3 K).measurable).mul ((measurable_wt K).comp (measurable_snd.comp measurable_fst))).mul
      ((measurable_R K).comp (continuous_const.mul (continuous_coord3 K)).measurable)

  have hζH : ∀ ζ : M4aHerbrand.principalIdeles (𝓞 K) K,
      centralScalar (𝓞 K) K ((ζ : M4aHerbrand.principalIdeles (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ) ∈ rationalCentreUnipotent K := by
    intro ζ
    obtain ⟨a, ha⟩ := ζ.2
    rw [← ha, ← ratCentral_eq_centralScalar]
    exact ratCentral_mem K a
  have hC : ∀ (ζ : M4aHerbrand.principalIdeles (𝓞 K) K) (u t : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
      f (coord3 K ((ζ⁻¹ • u, t), k)) * wt K t * R K (coord3 K ((ζ⁻¹ • u, t), k)) =
        Ψ (centralScalar (𝓞 K) K ((ζ⁻¹ : M4aHerbrand.principalIdeles (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ)) ((u, t), k) := by
    intro ζ u t k
    have hsplit : coord3 K ((ζ⁻¹ • u, t), k) =
        centralScalar (𝓞 K) K ((ζ⁻¹ : M4aHerbrand.principalIdeles (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ) * coord3 K ((u, t), k) := by
      simp only [coord3, Subgroup.smul_def, smul_eq_mul, map_mul, mul_assoc]
    simp only [hΨ_def, hsplit, hfH _ (hζH ζ⁻¹)]
  calc ∫⁻ u, ∫⁻ t, ∫⁻ k, f (coord3 K ((u, t), k)) * wt K t * R K (coord3 K ((u, t), k))
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
      = ∑' ζ : M4aHerbrand.principalIdeles (𝓞 K) K, ∫⁻ u in D, ∫⁻ t, ∫⁻ k,
          Ψ (centralScalar (𝓞 K) K ((ζ⁻¹ : M4aHerbrand.principalIdeles (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ)) ((u, t), k)
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
        rw [hFD.lintegral_eq_tsum']
        simp_rw [hC]
    _ = ∫⁻ u in D, ∑' ζ : M4aHerbrand.principalIdeles (𝓞 K) K, ∫⁻ t, ∫⁻ k,
          Ψ (centralScalar (𝓞 K) K ((ζ⁻¹ : M4aHerbrand.principalIdeles (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ)) ((u, t), k)
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
        rw [lintegral_tsum fun ζ => ?_]
        exact ((hΨ _).lintegral_prod_right'.lintegral_prod_right').aemeasurable
    _ = ∫⁻ u in D, ∫⁻ t, ∑' ζ : M4aHerbrand.principalIdeles (𝓞 K) K, ∫⁻ k,
          Ψ (centralScalar (𝓞 K) K ((ζ⁻¹ : M4aHerbrand.principalIdeles (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ)) ((u, t), k)
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
        refine lintegral_congr fun u => ?_
        rw [lintegral_tsum fun ζ => ?_]
        exact ((hΨ _).lintegral_prod_right'.comp (measurable_const.prodMk measurable_id)).aemeasurable
    _ = ∫⁻ u in D, ∫⁻ t, ∫⁻ k, ∑' ζ : M4aHerbrand.principalIdeles (𝓞 K) K,
          Ψ (centralScalar (𝓞 K) K ((ζ⁻¹ : M4aHerbrand.principalIdeles (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ)) ((u, t), k)
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
        refine lintegral_congr fun u => lintegral_congr fun t => ?_
        rw [lintegral_tsum fun ζ => ?_]
        exact ((hΨ _).comp (measurable_const.prodMk measurable_id)).aemeasurable
    _ = ∫⁻ u in D, ∫⁻ t, ∫⁻ k, f (coord3 K ((u, t), k)) * wt K t * (adelicAddHaar (𝓞 K) K) (adelicBox K)
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
        refine lintegral_congr fun u => lintegral_congr fun t => lintegral_congr fun k => ?_
        simp only [hΨ_def]
        rw [ENNReal.tsum_mul_left]
        congr 1
        simp only [R]
        exact tsum_lintegral_density K (coord3 K ((u, t), k))
    _ = _ := by
        have e : ∀ (u t : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
            f (coord3 K ((u, t), k)) * wt K t * (adelicAddHaar (𝓞 K) K) (adelicBox K) =
              (adelicAddHaar (𝓞 K) K) (adelicBox K) *
                (f (centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)) := fun u t k => by
          simp only [coord3, wt]; ring
        simp_rw [e, lintegral_const_mul' _ _ hboxtop]

end IwasawaQuot
p2m_reactivate "P2MW.S_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.AutomorphicForm.IwasawaQuot"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.AutomorphicForm.IwasawaQuot P2MW.S_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.AutomorphicForm.IwasawaQuot P2MW.S_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.AutomorphicForm"

theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ (D : Set (NumberField.AdeleRing (𝓞 K) K)ˣ), MeasurableSet D →
        MeasureTheory.IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) →
      ∀ f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
        (∀ x ∈ AutomorphicForm.rationalCentreUnipotent K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(AutomorphicForm.rationalCentreUnipotentQuotientMeasure K) =
          c * ∫⁻ z in D, ∫⁻ t, ∫⁻ k,
                f (AutomorphicForm.centralScalar (𝓞 K) K z * NumberField.AdelicLevel.diagOne t * (k : AutomorphicForm.AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(AutomorphicForm.maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) :=
  AutomorphicForm.IwasawaQuot.main K

end S_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
end P2MW
export P2MW.S_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa (solution)
