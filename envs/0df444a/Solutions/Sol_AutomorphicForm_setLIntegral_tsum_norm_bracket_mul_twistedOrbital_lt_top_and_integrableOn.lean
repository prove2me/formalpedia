-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_tsum_norm_bracket_mul_twistedOrbital_lt_top_and_integrableOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f8808d7f-2c88-519e-8d2a-7d4f20eb44a7

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining

import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_exists_mem_mul_of_inv_mul_globalPoints_mul_sigmaAdelicAct_centralScalar_mul_mem_of_diagonal
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
import Theorems.Thm_AutomorphicForm_integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_diagOne_mul
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_ideleNorm_unitsAct
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
import Theorems.Thm_AutomorphicForm_mem_twistedStabilizer_iff_diagonal_or_antidiagonal
import Theorems.Thm_AutomorphicForm_exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure
import Theorems.Thm_AutomorphicForm_exists_pos_isFundamentalDomain_forall_setIntegral_indicator_slab_bracket_eq_mul_of_sigmaCentraliser
import Theorems.Thm_AutomorphicForm_lintegral_abs_twistedOrbital_lt_top_and_integrable_norm_and_weighted_and_exists_height_mul_le_of_zpowers
import Theorems.Thm_AutomorphicForm_setLIntegral_tsum_comp_globalPoints_inv_mul_eq_lintegral_haarQuotient_setLIntegral_of_subgroup
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setLIntegral_tsum_norm_bracket_mul_twistedOrbital_lt_top_and_integrableOn
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicHeight NumberField.TateGlobal AutomorphicForm
open scoped Pointwise ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace FDTOrbAbs

section Height

variable (L : Type) [Field L] [NumberField L]

theorem val_mul_apply' (x y : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((x * y : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i 0 * (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 j +
        (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i 1 * (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem adelicWeyl_val :
    ((adelicWeyl (𝓞 L) L : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = !![0, 1; 1, 0] := by
  ext i j
  show algebraMap L (AdeleRing (𝓞 L) L) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) L) i j) = _
  fin_cases i <;> fin_cases j <;> simp

theorem adelicWeyl_inv : (adelicWeyl (𝓞 L) L)⁻¹ = adelicWeyl (𝓞 L) L := by
  unfold adelicWeyl
  rw [← map_inv, gl2Weyl_inv]

theorem weyl_conj_diag (h : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0) :
    ((adelicWeyl (𝓞 L) L * h * (adelicWeyl (𝓞 L) L)⁻¹ : AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      !![(h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1, 0; 0, (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0] := by
  rw [adelicWeyl_inv]
  ext i j
  simp only [val_mul_apply', adelicWeyl_val, h10, h01]
  fin_cases i <;> fin_cases j <;> simp

theorem ideleNorm_inv' (w : (AdeleRing (𝓞 L) L)ˣ) : ideleNorm L w⁻¹ = (ideleNorm L w)⁻¹ := by
  have h1 : ideleNorm L 1 = 1 := by
    have := ideleNorm_mul (F := L) 1 1
    rw [mul_one] at this
    have hp := ideleNorm_pos (F := L) 1
    nlinarith [this, hp]
  have := ideleNorm_mul (F := L) w⁻¹ w
  rw [inv_mul_cancel, h1] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem adelicHeight_borel_mul {b : AdelicGL2 (𝓞 L) L} (hb : b ∈ adelicBorel (𝓞 L) L)
    (hb01 : (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0) (g : AdelicGL2 (𝓞 L) L) :
    adelicHeight L (b * g)
      = ideleNorm L (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L)))
        * (ideleNorm L (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))))⁻¹
        * adelicHeight L g := by
  set u := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L)) with hu
  set v := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L)) with hv
  have hb10 : (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 := hb
  have hu' : ((u : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 :=
    borelDiagFst_apply_val _
  have hv' : ((v : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 :=
    borelDiagSnd_apply_val _
  have hdec : b = centralScalar (𝓞 L) L v * diagOne (u * v⁻¹) := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    simp only [val_mul_apply', NumberField.AdelicVolume.centralScalar_val, diagOne_coe_apply]
    fin_cases i <;> fin_cases j
    · simp [Matrix.diagonal, ← hu']
      first | done | (rw [mul_left_comm, Units.mul_inv, mul_one])
    · simp [Matrix.diagonal, hb01]
    · simp [Matrix.diagonal, hb10]
    · simp [Matrix.diagonal, ← hv']
  rw [hdec, mul_assoc, (NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul L).2,
    NumberField.AdelicHeight.adelicHeight_diagOne_mul, ideleNorm_mul, ideleNorm_inv']

theorem height_prod_diag_mul (h y : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0) :
    adelicHeight L (h * y) * adelicHeight L (adelicWeyl (𝓞 L) L * (h * y)) =
      adelicHeight L y * adelicHeight L (adelicWeyl (𝓞 L) L * y) := by
  set w := adelicWeyl (𝓞 L) L with hw
  have hb : h ∈ adelicBorel (𝓞 L) L := h10
  set h' : AdelicGL2 (𝓞 L) L := w * h * w⁻¹ with hh'
  have hval := weyl_conj_diag L h h10 h01
  rw [← hh'] at hval
  have hb' : h' ∈ adelicBorel (𝓞 L) L := by
    show (h' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0
    rw [hval]; simp
  have hb'01 : (h' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 := by
    rw [hval]; simp
  have e1 : w * (h * y) = h' * (w * y) := by rw [hh']; group
  rw [e1, adelicHeight_borel_mul L hb h01, adelicHeight_borel_mul L hb' hb'01]
  have hF : borelDiagFst (⟨h', hb'⟩ : ↥(adelicBorel (𝓞 L) L)) = borelDiagSnd (⟨h, hb⟩ : ↥(adelicBorel (𝓞 L) L)) := by
    apply Units.ext
    rw [borelDiagFst_apply_val, borelDiagSnd_apply_val]
    show (h' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = _
    rw [hval]; simp
  have hS : borelDiagSnd (⟨h', hb'⟩ : ↥(adelicBorel (𝓞 L) L)) = borelDiagFst (⟨h, hb⟩ : ↥(adelicBorel (𝓞 L) L)) := by
    apply Units.ext
    rw [borelDiagFst_apply_val, borelDiagSnd_apply_val]
    show (h' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = _
    rw [hval]; simp
  rw [hF, hS]
  have h1 : 0 < ideleNorm L (borelDiagFst (⟨h, hb⟩ : ↥(adelicBorel (𝓞 L) L))) := ideleNorm_pos _
  have h2 : 0 < ideleNorm L (borelDiagSnd (⟨h, hb⟩ : ↥(adelicBorel (𝓞 L) L))) := ideleNorm_pos _
  field_simp

def hgt (y : AdelicGL2 (𝓞 L) L) : ℝ := adelicHeight L y * adelicHeight L (adelicWeyl (𝓞 L) L * y)

theorem hgt_pos (y : AdelicGL2 (𝓞 L) L) : 0 < hgt L y := mul_pos (adelicHeight_pos y) (adelicHeight_pos _)

theorem continuous_hgt : Continuous (hgt L) :=
  (NumberField.AdelicHeight.continuous_adelicHeight L).mul
    ((NumberField.AdelicHeight.continuous_adelicHeight L).comp (continuous_const.mul continuous_id))

theorem hgt_diag_mul (h y : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0) :
    hgt L (h * y) = hgt L y := height_prod_diag_mul L h y h10 h01

theorem neg_log_sub_log_eq (y : AdelicGL2 (𝓞 L) L) :
    -Real.log (adelicHeight L y) - Real.log (adelicHeight L (adelicWeyl (𝓞 L) L * y)) = -Real.log (hgt L y) := by
  rw [hgt, Real.log_mul (adelicHeight_pos y).ne' (adelicHeight_pos _).ne']
  ring

end Height

section Algebra

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem sigmaAdelicAct_apply (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L D σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) := rfl

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem _root_.FDTOrbAbs.centralScalar_val (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((centralScalar (𝓞 L) L z : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      !![(z : AdeleRing (𝓞 L) L), 0; 0, (z : AdeleRing (𝓞 L) L)] := by
  ext i j
  change Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j = _
  fin_cases i <;> fin_cases j <;> simp

p2m_export "FDTOrbAbs" "centralScalar_val"
theorem centralScalar_inv_val (z : (AdeleRing (𝓞 L) L)ˣ) :
    (((centralScalar (𝓞 L) L z)⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 =
      ((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) := by
  rw [← map_inv, centralScalar_val]; simp

theorem continuous_matrix_two {A X : Type*} [TopologicalSpace A] [TopologicalSpace X] {f : X → Matrix (Fin 2) (Fin 2) A}
    (h00 : Continuous fun x => f x 0 0) (h01 : Continuous fun x => f x 0 1)
    (h10 : Continuous fun x => f x 1 0) (h11 : Continuous fun x => f x 1 1) : Continuous f := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 L) L : (AdeleRing (𝓞 L) L)ˣ → AdelicGL2 (𝓞 L) L) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine (continuous_matrix_two ?_ ?_ ?_ ?_ :
      Continuous fun z : (AdeleRing (𝓞 L) L)ˣ =>
        (!![(z : AdeleRing (𝓞 L) L), 0; 0, (z : AdeleRing (𝓞 L) L)] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).congr
      fun z => (centralScalar_val z).symm
    · simpa using Units.continuous_val
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using Units.continuous_val
  · refine (continuous_matrix_two ?_ ?_ ?_ ?_ :
      Continuous fun z : (AdeleRing (𝓞 L) L)ˣ =>
        (!![((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), 0; 0, ((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)] :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).congr
      fun z => ?_
    · simpa using Units.continuous_coe_inv
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using Units.continuous_coe_inv
    · show _ = (((centralScalar (𝓞 L) L z)⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))
      rw [← map_inv, centralScalar_val]

theorem continuous_val_apply (i j : Fin 2) :
    Continuous fun g : AdelicGL2 (𝓞 L) L => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j :=
  Units.continuous_val.matrix_elem i j

theorem continuous_val_inv_apply (i j : Fin 2) :
    Continuous fun g : AdelicGL2 (𝓞 L) L => ((g⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j :=
  Units.continuous_coe_inv.matrix_elem i j

theorem continuous_unitsAct (τ : L ≃ₐ[K] L) : Continuous (D.unitsAct τ : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 L) L)ˣ) :=
  Continuous.units_map _ (D.continuous_act τ)

theorem unitsAct_inv_apply (w : (AdeleRing (𝓞 L) L)ˣ) : D.unitsAct σ⁻¹ (D.unitsAct σ w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem unitsAct_unitsAct_inv (w : (AdeleRing (𝓞 L) L)ˣ) : D.unitsAct σ (D.unitsAct σ⁻¹ w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem exists_isCompact_centralScalar_mem (M : Set (AdelicGL2 (𝓞 L) L)) (hM : IsCompact M) :
    ∃ S : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact S ∧ ∀ u : (AdeleRing (𝓞 L) L)ˣ, centralScalar (𝓞 L) L u ∈ M → u ∈ S := by
  set v : AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L := fun g => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 with hv
  set vi : AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L :=
    fun g => ((g⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 with hvi
  refine ⟨(Units.embedProduct (AdeleRing (𝓞 L) L)) ⁻¹' ((v '' M) ×ˢ (MulOpposite.op '' (vi '' M))), ?_, ?_⟩
  · exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
      ((hM.image (continuous_val_apply 0 0)).prod ((hM.image (continuous_val_inv_apply 0 0)).image
        MulOpposite.continuous_op))
  · intro u hu
    rw [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
    refine ⟨⟨_, hu, ?_⟩, ⟨vi (centralScalar (𝓞 L) L u), ⟨_, hu, rfl⟩, ?_⟩⟩
    · show ((centralScalar (𝓞 L) L u : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = u
      rw [centralScalar_val]; simp
    · show MulOpposite.op ((((centralScalar (𝓞 L) L u)⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0) = _
      rw [centralScalar_inv_val]

end Algebra

section Invariance

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]

def xiTop (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ where
  toFun z := ξL ⟨z, Subgroup.mem_top z⟩
  map_one' := by exact map_one ξL
  map_mul' a b := by rw [← map_mul]; rfl

theorem xiTop_apply (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    xiTop ξL z = ξL ⟨z, Subgroup.mem_top z⟩ := rfl

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
  (δ₀ : GL (Fin 2) L) (φ : AdelicGL2 (𝓞 L) L → ℂ)

private def _root_.FDTOrbAbs.orb (y : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
    φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) ∂νZL

p2m_export "FDTOrbAbs" "orb"

theorem orb_mul_eq (g y : AdelicGL2 (𝓞 L) L) (m : (AdeleRing (𝓞 L) L)ˣ)
    (hg : g⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ g =
      globalPoints (𝓞 L) L δ₀ * centralScalar (𝓞 L) L m) :
    orb νZL D σ ξL δ₀ φ (g * y) =
      (((xiTop ξL (D.unitsAct σ⁻¹ m))⁻¹ : ℂˣ) : ℂ) * orb νZL D σ ξL δ₀ φ y :=
  AutomorphicForm.integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar
    K L D σ νZL (xiTop ξL) φ _ g y m hg

theorem val_mul_apply (x y : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((x * y : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i 0 * (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 j +
        (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i 1 * (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem diag_comm (x y : AdelicGL2 (𝓞 L) L)
    (hx10 : (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0) (hx01 : (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0)
    (hy10 : (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0) (hy01 : (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0) :
    x * y = y * x := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [val_mul_apply, val_mul_apply]
  fin_cases i <;> fin_cases j <;> simp [hx10, hx01, hy10, hy01, mul_comm]

def diagUnit11 (h : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0) : (AdeleRing (𝓞 L) L)ˣ :=
  borelDiagSnd (⟨h, h10⟩ : ↥(adelicBorel (𝓞 L) L))

include δ₀ in
omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] in
theorem coe_diagUnit11 (h : AdelicGL2 (𝓞 L) L) (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0) :
    ((diagUnit11 h h10 : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 := rfl

variable (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)

include hδ₀u hδ₀l in

theorem exists_key_of_diag_of_mem_center (h : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0)
    (hcen : sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)) :
    ∃ u mm : (AdeleRing (𝓞 L) L)ˣ, mm = D.unitsAct σ u * u⁻¹ ∧
      h⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ h =
        globalPoints (𝓞 L) L δ₀ * centralScalar (𝓞 L) L mm := by
  set gp := globalPoints (𝓞 L) L with hgp
  set sh := sigmaAdelicAct K L D σ h with hsh
  have hcen' := hcen
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen'
  obtain ⟨mm, hmm⟩ := hcen'
  have hmm' : centralScalar (𝓞 L) L mm = sh * h⁻¹ := hmm
  have hcs : centralScalar (𝓞 L) L mm ∈ Subgroup.center (AdelicGL2 (𝓞 L) L) := by
    rw [hmm']; exact hcen
  have e1 : sh = centralScalar (𝓞 L) L mm * h := by rw [hmm', inv_mul_cancel_right]
  have e2 : gp δ₀ * h = h * gp δ₀ := by
    refine diag_comm _ _ ?_ ?_ h10 h01
    · show algebraMap L (AdeleRing (𝓞 L) L) ((δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0) = 0
      rw [hδ₀u, map_zero]
    · show algebraMap L (AdeleRing (𝓞 L) L) ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1) = 0
      rw [hδ₀l, map_zero]
  have e3 : centralScalar (𝓞 L) L mm * h = h * centralScalar (𝓞 L) L mm :=
    (Subgroup.mem_center_iff.1 hcs h).symm
  have key : h⁻¹ * gp δ₀ * sh = gp δ₀ * centralScalar (𝓞 L) L mm := by
    calc h⁻¹ * gp δ₀ * sh = h⁻¹ * gp δ₀ * (centralScalar (𝓞 L) L mm * h) := by rw [e1]
      _ = h⁻¹ * (gp δ₀ * h) * centralScalar (𝓞 L) L mm := by rw [e3]; group
      _ = gp δ₀ * centralScalar (𝓞 L) L mm := by rw [e2]; group
  set hu : (AdeleRing (𝓞 L) L)ˣ := diagUnit11 h h10 with hhu
  have hmm_eq : mm = D.unitsAct σ hu * hu⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    have hval := congrArg (fun M : AdelicGL2 (𝓞 L) L => (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1) e1
    rw [hsh, sigmaAdelicAct_apply, val_mul_apply, centralScalar_val] at hval
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', zero_mul, zero_add] at hval
    rw [Units.val_mul]
    exact hval.symm
  exact ⟨hu, mm, hmm_eq, key⟩

include hδ₀u hδ₀l in
theorem orb_mul_of_diag_of_mem_center' (h : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0)
    (hcen : sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L))
    (y : AdelicGL2 (𝓞 L) L) :
    ∃ u : (AdeleRing (𝓞 L) L)ˣ, orb νZL D σ ξL δ₀ φ (h * y) =
      (((xiTop ξL (D.unitsAct σ⁻¹ (D.unitsAct σ u * u⁻¹)))⁻¹ : ℂˣ) : ℂ) * orb νZL D σ ξL δ₀ φ y := by
  obtain ⟨u, mm, hmm, key⟩ := exists_key_of_diag_of_mem_center D σ δ₀ hδ₀u hδ₀l h h10 h01 hcen
  exact ⟨u, by rw [orb_mul_eq νZL D σ ξL δ₀ φ h y mm key, hmm]⟩

end Invariance

section AbsValue

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
  (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
  (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)

include hξc hξt in

theorem norm_xiTop_eq_one (v : (AdeleRing (𝓞 L) L)ˣ) (hv : v ∈ normOneIdeles L) :
    ‖((xiTop ξL v : ℂˣ) : ℂ)‖ = 1 := by
  have hN1 : ∀ a b : (AdeleRing (𝓞 L) L)ˣ,
      ‖((xiTop ξL (a * b) : ℂˣ) : ℂ)‖ = ‖((xiTop ξL a : ℂˣ) : ℂ)‖ * ‖((xiTop ξL b : ℂˣ) : ℂ)‖ := by
    intro a b; rw [map_mul, Units.val_mul, norm_mul]
  have hNpos : ∀ a, 0 < ‖((xiTop ξL a : ℂˣ) : ℂ)‖ := fun a => norm_pos_iff.mpr (Units.ne_zero _)
  have hNprin : ∀ η : Lˣ,
      ‖((xiTop ξL (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) η) : ℂˣ) : ℂ)‖ = 1 := by
    intro η
    rw [xiTop_apply, hξt _ ⟨η, rfl⟩, Units.val_one, norm_one]
  obtain ⟨Kc, hKc, -, hrep⟩ :=
    NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul L
  have hcontN : Continuous fun a : (AdeleRing (𝓞 L) L)ˣ => ‖((xiTop ξL a : ℂˣ) : ℂ)‖ := hξc.norm
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcontN.continuousOn
  have hbound : ∀ w ∈ normOneIdeles L, ‖((xiTop ξL w : ℂˣ) : ℂ)‖ ≤ B := by
    intro w hw
    obtain ⟨η, κ, hκ, hwk⟩ := hrep w hw
    rw [hwk, hN1]
    have : ‖((xiTop ξL (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom η) : ℂˣ) : ℂ)‖ = 1 := hNprin η
    rw [this, one_mul]
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB κ hκ))
  have hle : ∀ w ∈ normOneIdeles L, ‖((xiTop ξL w : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro w hw
    by_contra hgt
    push_neg at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hgt
    have hpow : ‖((xiTop ξL (w ^ n) : ℂˣ) : ℂ)‖ = ‖((xiTop ξL w : ℂˣ) : ℂ)‖ ^ n := by
      rw [map_pow, Units.val_pow_eq_pow_val, norm_pow]
    have := hbound (w ^ n) (pow_mem hw n)
    rw [hpow] at this
    linarith
  refine le_antisymm (hle v hv) ?_
  have h1 := hle v⁻¹ (inv_mem hv)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h1
  exact (inv_le_one₀ (hNpos v)).mp h1

omit hξc hξt in
theorem mem_normOneIdeles_coboundary (u : (AdeleRing (𝓞 L) L)ˣ) :
    D.unitsAct σ⁻¹ (D.unitsAct σ u * u⁻¹) ∈ normOneIdeles L := by
  rw [mem_normOneIdeles_iff, M4aHerbrand.IdeleGaloisDescent.ideleNorm_unitsAct, ideleNorm_mul,
    M4aHerbrand.IdeleGaloisDescent.ideleNorm_unitsAct, ideleNorm_inv' L, mul_inv_cancel₀ (ideleNorm_pos (F := L) u).ne']

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
  (δ₀ : GL (Fin 2) L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
  (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)

include hξc hξt hδ₀u hδ₀l in

theorem norm_orb_mul_of_diag_of_mem_center (h : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0)
    (hcen : sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L))
    (y : AdelicGL2 (𝓞 L) L) :
    ‖orb νZL D σ ξL δ₀ φ (h * y)‖ = ‖orb νZL D σ ξL δ₀ φ y‖ := by
  obtain ⟨u, hu⟩ := orb_mul_of_diag_of_mem_center' νZL D σ ξL δ₀ φ hδ₀u hδ₀l h h10 h01 hcen y
  rw [hu, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
    norm_xiTop_eq_one ξL hξc hξt _ (mem_normOneIdeles_coboundary D σ u), inv_one, one_mul]

def orbAbs (y : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
    ‖φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y))‖ₑ ∂νZL

theorem enorm_orb_le_orbAbs (y : AdelicGL2 (𝓞 L) L) :
    ‖orb νZL D σ ξL δ₀ φ y‖ₑ ≤ orbAbs D σ ξL νZL δ₀ φ y := by
  unfold orb orbAbs
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1
  funext z
  rw [enorm_mul]

theorem orbAbs_eq_zero_of_forall (y : AdelicGL2 (𝓞 L) L)
    (h0 : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) = 0) :
    orbAbs D σ ξL νZL δ₀ φ y = 0 := by
  unfold orbAbs
  simp only [h0, enorm_zero, mul_zero, lintegral_zero]

omit [νZL.IsHaarMeasure] in
theorem centralScalar_comm' (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L z * g = g * centralScalar (𝓞 L) L z := by
  have : centralScalar (𝓞 L) L z ∈ Subgroup.center (AdelicGL2 (𝓞 L) L) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨z, rfl⟩
  exact ((Subgroup.mem_center_iff.mp this) g).symm

include hξc hξt hδ₀u hδ₀l in

theorem orbAbs_mul_of_diag_of_mem_center [MeasurableMul (AdeleRing (𝓞 L) L)ˣ] (h : AdelicGL2 (𝓞 L) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0)
    (hcen : sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L))
    (y : AdelicGL2 (𝓞 L) L) :
    orbAbs D σ ξL νZL δ₀ φ (h * y) = orbAbs D σ ξL νZL δ₀ φ y := by
  obtain ⟨u, mm, hmm, key⟩ := exists_key_of_diag_of_mem_center D σ δ₀ hδ₀u hδ₀l h h10 h01 hcen
  set m' : (AdeleRing (𝓞 L) L)ˣ := D.unitsAct σ⁻¹ mm with hm'
  have hm'mem : m' ∈ normOneIdeles L := by
    rw [hm', hmm]; exact mem_normOneIdeles_coboundary D σ u
  have hm'1 : ‖((ξL ⟨m'⁻¹, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ₑ = 1 := by
    rw [← xiTop_apply, ← ofReal_norm, norm_xiTop_eq_one ξL hξc hξt _ (inv_mem hm'mem), ENNReal.ofReal_one]
  have harg : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      (h * y)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * (h * y)) =
        y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (m' * z) * y) := by
    intro z
    rw [map_mul (sigmaAdelicAct K L D σ), map_mul (sigmaAdelicAct K L D σ), sigmaAdelicAct_centralScalar,
      map_mul (sigmaAdelicAct K L D σ), sigmaAdelicAct_centralScalar, map_mul (D.unitsAct σ), hm',
      unitsAct_unitsAct_inv, map_mul (centralScalar (𝓞 L) L)]
    calc (h * y)⁻¹ * globalPoints (𝓞 L) L δ₀ *
          (centralScalar (𝓞 L) L (D.unitsAct σ z) * (sigmaAdelicAct K L D σ h * sigmaAdelicAct K L D σ y))
        = y⁻¹ * (h⁻¹ * globalPoints (𝓞 L) L δ₀ *
            (centralScalar (𝓞 L) L (D.unitsAct σ z) * sigmaAdelicAct K L D σ h)) * sigmaAdelicAct K L D σ y := by group
      _ = y⁻¹ * (h⁻¹ * globalPoints (𝓞 L) L δ₀ *
            (sigmaAdelicAct K L D σ h * centralScalar (𝓞 L) L (D.unitsAct σ z))) * sigmaAdelicAct K L D σ y := by
          rw [centralScalar_comm']
      _ = y⁻¹ * (h⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ h) *
            centralScalar (𝓞 L) L (D.unitsAct σ z) * sigmaAdelicAct K L D σ y := by group
      _ = y⁻¹ * (globalPoints (𝓞 L) L δ₀ * centralScalar (𝓞 L) L mm) *
            centralScalar (𝓞 L) L (D.unitsAct σ z) * sigmaAdelicAct K L D σ y := by rw [key]
      _ = y⁻¹ * globalPoints (𝓞 L) L δ₀ *
            (centralScalar (𝓞 L) L mm * centralScalar (𝓞 L) L (D.unitsAct σ z) * sigmaAdelicAct K L D σ y) := by group
  set G : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞ := fun w => ‖((xiTop ξL (m'⁻¹ * w) : ℂˣ) : ℂ)‖ₑ *
    ‖φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L w * y))‖ₑ with hG
  unfold orbAbs
  simp only [harg]
  have step : (fun z : (AdeleRing (𝓞 L) L)ˣ => ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
      ‖φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (m' * z) * y))‖ₑ) =
      fun z => G (m' * z) := by
    funext z
    simp only [hG, inv_mul_cancel_left, xiTop_apply]
  rw [step, lintegral_mul_left_eq_self]
  simp only [hG, map_mul, Units.val_mul, enorm_mul, xiTop_apply, hm'1, one_mul]

end AbsValue

section Continuity

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
  [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
  (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
  (δ₀ : GL (Fin 2) L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)

theorem locallyCompactSpace_ideles : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

include hξc hφc hφs in

theorem continuous_orb : Continuous (orb νZL D σ ξL δ₀ φ) := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := locallyCompactSpace_ideles
  set gp := globalPoints (𝓞 L) L with hgp
  set σA := sigmaAdelicAct K L D σ with hσA
  set cs := centralScalar (𝓞 L) L with hcs
  set I : AdelicGL2 (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ℂ := fun y z =>
    ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (y⁻¹ * gp δ₀ * σA (cs z * y)) with hI
  have harg : Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => p.1⁻¹ * gp δ₀ * σA (cs p.2 * p.1) :=
    ((continuous_fst.inv).mul continuous_const).mul
      ((continuous_sigmaAdelicAct K L D σ).comp ((continuous_centralScalar.comp continuous_snd).mul continuous_fst))
  have hIc : Continuous (Function.uncurry I) := (hξc.comp continuous_snd).mul (hφc.comp harg)
  rw [continuous_iff_continuousAt]
  intro y₀
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds y₀
  set C := tsupport φ with hC
  have hCc : IsCompact C := hφs.isCompact
  set M : Set (AdelicGL2 (𝓞 L) L) :=
    (fun p : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L => (gp δ₀)⁻¹ * p.1 * p.2.1 * p.2.2⁻¹) ''
      (N ×ˢ C ×ˢ (σA '' N)) with hM
  have hMc : IsCompact M :=
    (hNc.prod (hCc.prod (hNc.image (continuous_sigmaAdelicAct K L D σ)))).image
      (((continuous_const.mul continuous_fst).mul (continuous_fst.comp continuous_snd)).mul
        (continuous_snd.comp continuous_snd).inv)
  obtain ⟨S, hSc, hS⟩ := exists_isCompact_centralScalar_mem M hMc
  set S' : Set (AdeleRing (𝓞 L) L)ˣ := (D.unitsAct σ⁻¹) '' S with hS'
  have hS'c : IsCompact S' := hSc.image (continuous_unitsAct D σ⁻¹)
  have hvanish : ∀ y ∈ N, ∀ z ∉ S', I y z = 0 := by
    intro y hy z hz
    by_contra hne
    apply hz
    have hφne : φ (y⁻¹ * gp δ₀ * σA (cs z * y)) ≠ 0 := right_ne_zero_of_mul hne
    have hmem : y⁻¹ * gp δ₀ * σA (cs z * y) ∈ C := subset_tsupport _ (Function.mem_support.2 hφne)
    have hcsM : cs (D.unitsAct σ z) ∈ M := by
      refine ⟨(y, y⁻¹ * gp δ₀ * σA (cs z * y), σA y), ⟨hy, hmem, ⟨y, hy, rfl⟩⟩, ?_⟩
      show (gp δ₀)⁻¹ * y * (y⁻¹ * gp δ₀ * σA (cs z * y)) * (σA y)⁻¹ = cs (D.unitsAct σ z)
      rw [hcs, ← sigmaAdelicAct_centralScalar D σ, ← hσA, map_mul]
      group
    exact ⟨D.unitsAct σ z, hS _ hcsM, unitsAct_inv_apply D σ z⟩
  have heq : ∀ y ∈ N, ∫ z in S', I y z ∂νZL = orb νZL D σ ξL δ₀ φ y := fun y hy =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => hvanish y hy z hz
  have hcont : Continuous fun y => ∫ z in S', I y z ∂νZL := continuous_parametric_integral_of_continuous hIc hS'c
  refine (hcont.continuousAt (x := y₀)).congr ?_
  filter_upwards [hN] with y hy
  exact heq y hy

include hξc hφc hφs in

theorem orbAbs_le_of_isCompact (N : Set (AdelicGL2 (𝓞 L) L)) (hNc : IsCompact N) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ y ∈ N, orbAbs D σ ξL νZL δ₀ φ y ≤ B := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := locallyCompactSpace_ideles
  set gp := globalPoints (𝓞 L) L with hgp
  set σA := sigmaAdelicAct K L D σ with hσA
  set cs := centralScalar (𝓞 L) L with hcs
  set I : AdelicGL2 (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ℂ := fun y z =>
    ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (y⁻¹ * gp δ₀ * σA (cs z * y)) with hI
  have harg : Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => p.1⁻¹ * gp δ₀ * σA (cs p.2 * p.1) :=
    ((continuous_fst.inv).mul continuous_const).mul
      ((continuous_sigmaAdelicAct K L D σ).comp ((continuous_centralScalar.comp continuous_snd).mul continuous_fst))
  have hIc : Continuous (Function.uncurry I) := (hξc.comp continuous_snd).mul (hφc.comp harg)
  set C := tsupport φ with hC
  have hCc : IsCompact C := hφs.isCompact
  set M : Set (AdelicGL2 (𝓞 L) L) :=
    (fun p : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L => (gp δ₀)⁻¹ * p.1 * p.2.1 * p.2.2⁻¹) ''
      (N ×ˢ C ×ˢ (σA '' N)) with hM
  have hMc : IsCompact M :=
    (hNc.prod (hCc.prod (hNc.image (continuous_sigmaAdelicAct K L D σ)))).image
      (((continuous_const.mul continuous_fst).mul (continuous_fst.comp continuous_snd)).mul
        (continuous_snd.comp continuous_snd).inv)
  obtain ⟨S, hSc, hS⟩ := exists_isCompact_centralScalar_mem M hMc
  set S' : Set (AdeleRing (𝓞 L) L)ˣ := (D.unitsAct σ⁻¹) '' S with hS'
  have hS'c : IsCompact S' := hSc.image (continuous_unitsAct D σ⁻¹)
  have hvanish : ∀ y ∈ N, ∀ z ∉ S', I y z = 0 := by
    intro y hy z hz
    by_contra hne
    apply hz
    have hφne : φ (y⁻¹ * gp δ₀ * σA (cs z * y)) ≠ 0 := right_ne_zero_of_mul hne
    have hmem : y⁻¹ * gp δ₀ * σA (cs z * y) ∈ C := subset_tsupport _ (Function.mem_support.2 hφne)
    have hcsM : cs (D.unitsAct σ z) ∈ M := by
      refine ⟨(y, y⁻¹ * gp δ₀ * σA (cs z * y), σA y), ⟨hy, hmem, ⟨y, hy, rfl⟩⟩, ?_⟩
      show (gp δ₀)⁻¹ * y * (y⁻¹ * gp δ₀ * σA (cs z * y)) * (σA y)⁻¹ = cs (D.unitsAct σ z)
      rw [hcs, ← sigmaAdelicAct_centralScalar D σ, ← hσA, map_mul]
      group
    exact ⟨D.unitsAct σ z, hS _ hcsM, unitsAct_inv_apply D σ z⟩
  obtain ⟨B₀, hB₀⟩ := (hNc.prod hS'c).exists_bound_of_continuousOn hIc.continuousOn
  refine ⟨ENNReal.ofReal B₀ * νZL S', ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS'c.measure_lt_top, fun y hy => ?_⟩
  have hle : ∀ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ‖φ (y⁻¹ * gp δ₀ * σA (cs z * y))‖ₑ ≤
      S'.indicator (fun _ => ENNReal.ofReal B₀) z := by
    intro z
    rw [← enorm_mul]
    by_cases hz : z ∈ S'
    · rw [Set.indicator_of_mem hz, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB₀ (y, z) ⟨hy, hz⟩)
    · have h0 : ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (y⁻¹ * gp δ₀ * σA (cs z * y)) = 0 := by
        simpa only [hI] using hvanish y hy z hz
      rw [h0, enorm_zero]
      exact bot_le
  calc orbAbs D σ ξL νZL δ₀ φ y ≤ ∫⁻ z, S'.indicator (fun _ => ENNReal.ofReal B₀) z ∂νZL := lintegral_mono hle
    _ = ENNReal.ofReal B₀ * νZL S' := lintegral_indicator_const hS'c.isClosed.measurableSet _

end Continuity

end FDTOrbAbs

namespace FDTB3

open AutomorphicForm NumberField.AdelicHeight

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]

def xiTop (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ where
  toFun z := ξL ⟨z, Subgroup.mem_top z⟩
  map_one' := by exact map_one ξL
  map_mul' a b := by rw [← map_mul]; rfl

theorem xiTop_apply (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    xiTop ξL z = ξL ⟨z, Subgroup.mem_top z⟩ := rfl

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
  (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
  (δ₀ : GL (Fin 2) L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
  (Λ : Subgroup (GL (Fin 2) L))
  (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))

private noncomputable def _root_.FDTB3.orb (y : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
    φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) ∂νZL

p2m_export "FDTB3" "orb"
omit [νZL.IsHaarMeasure] in
theorem globalPoints_scalar (ζ : Lˣ) :
    globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ) =
      centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ) := by
  ext i j
  simp only [AutomorphicForm.globalPoints, AutomorphicForm.centralScalar]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]

include hξt hΛ in

theorem orb_globalPoints_mul_of_mem (γ : GL (Fin 2) L) (hγ : γ ∈ Λ) (y : AdelicGL2 (𝓞 L) L) :
    orb νZL D σ ξL δ₀ φ (globalPoints (𝓞 L) L γ * y) = orb νZL D σ ξL δ₀ φ y := by
  have hcen := (hΛ γ).1 hγ
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen
  obtain ⟨ζ, hζ⟩ := hcen
  have hScen : Matrix.GeneralLinearGroup.scalar (Fin 2) ζ ∈ Subgroup.center (GL (Fin 2) L) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨ζ, rfl⟩
  have hcomm : ∀ g : GL (Fin 2) L, g * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * g := fun g => Subgroup.mem_center_iff.mp hScen g

  have key0 : γ⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) γ =
      δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ⁻¹ := by
    have e : γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹ =
        δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ := by
      rw [hζ]; group
    have hcommI : ∀ g : GL (Fin 2) L, g * (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)⁻¹ =
        (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)⁻¹ * g := fun g =>
      Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hScen) g
    calc γ⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) γ
        = γ⁻¹ * (δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ) * (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)⁻¹ *
            Matrix.GeneralLinearGroup.map (σ : L →+* L) γ := by group
      _ = γ⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) *
            (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) γ := by rw [← e]
      _ = δ₀ * ((Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹ *
            ((Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)) := by group
      _ = δ₀ * ((Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹ *
            (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ * (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)⁻¹)) := by
          rw [← hcommI]
      _ = δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ⁻¹ := by rw [map_inv]; group

  have key : (globalPoints (𝓞 L) L γ)⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L γ) =
      globalPoints (𝓞 L) L δ₀ * centralScalar (𝓞 L) L
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ⁻¹) := by
    have L2 : sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L γ) =
        globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) :=
      AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ γ
    rw [L2, ← globalPoints_scalar, ← map_inv, ← map_mul, ← map_mul, key0, map_mul]
  have hcov : orb νZL D σ ξL δ₀ φ (globalPoints (𝓞 L) L γ * y) =
      (((xiTop ξL (D.unitsAct σ⁻¹ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ⁻¹)))⁻¹ : ℂˣ) : ℂ) *
        orb νZL D σ ξL δ₀ φ y :=
    AutomorphicForm.integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar
      K L D σ νZL (xiTop ξL) φ _ _ y _ key
  have hprin : xiTop ξL (D.unitsAct σ⁻¹ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ⁻¹)) = 1 := by
    rw [xiTop_apply]
    apply hξt
    refine ⟨(σ⁻¹ : L ≃ₐ[K] L) (ζ⁻¹ : Lˣ) |> fun _ => Units.map ((σ⁻¹ : L ≃ₐ[K] L) : L →* L) ζ⁻¹, ?_⟩
    exact Units.ext (D.compat σ⁻¹ ((ζ⁻¹ : Lˣ) : L)).symm
  rw [hcov, hprin, inv_one, Units.val_one, one_mul]

section Bracket

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem val_mul_apply (x y : GL (Fin 2) L) (i j : Fin 2) :
    ((x * y : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
      (x : Matrix (Fin 2) (Fin 2) L) i 0 * (y : Matrix (Fin 2) (Fin 2) L) 0 j +
        (x : Matrix (Fin 2) (Fin 2) L) i 1 * (y : Matrix (Fin 2) (Fin 2) L) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem gl2Weyl_val : ((gl2Weyl : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![0, 1; 1, 0] := rfl

theorem adelicWeyl_eq : adelicWeyl (𝓞 L) L = globalPoints (𝓞 L) L gl2Weyl := rfl

theorem gl2Weyl_mul_self : (gl2Weyl : GL (Fin 2) L) * gl2Weyl = 1 := by
  rw [mul_eq_one_iff_eq_inv, gl2Weyl_inv]

theorem adelicHeight_globalPoints_mul_dichotomy
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ' : Subgroup (GL (Fin 2) L))
    (hΛ' : ∀ a : GL (Fin 2) L, a ∈ Λ' ↔ ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 0 / (a : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    (γ : GL (Fin 2) L) (hγ : γ ∈ Λ) (y : AdelicGL2 (𝓞 L) L) :
    (adelicHeight L (globalPoints (𝓞 L) L γ * y) = adelicHeight L y ∧
      adelicHeight L (adelicWeyl (𝓞 L) L * (globalPoints (𝓞 L) L γ * y)) = adelicHeight L (adelicWeyl (𝓞 L) L * y)) ∨
    (adelicHeight L (globalPoints (𝓞 L) L γ * y) = adelicHeight L (adelicWeyl (𝓞 L) L * y) ∧
      adelicHeight L (adelicWeyl (𝓞 L) L * (globalPoints (𝓞 L) L γ * y)) = adelicHeight L y) := by
  classical
  obtain ⟨-, hdich, -, -⟩ :=
    AutomorphicForm.mem_twistedStabilizer_iff_diagonal_or_antidiagonal K L σ hgen δ₀ hδ₀u hδ₀l hreg Λ hΛ Λ' hΛ'
  have hw : adelicWeyl (𝓞 L) L = globalPoints (𝓞 L) L gl2Weyl := rfl
  have hww : globalPoints (𝓞 L) L (gl2Weyl : GL (Fin 2) L) * globalPoints (𝓞 L) L gl2Weyl = 1 := by
    rw [← map_mul, gl2Weyl_mul_self, map_one]

  have hconj10 : ∀ g : GL (Fin 2) L, (((gl2Weyl * g * gl2Weyl : GL (Fin 2) L)) : Matrix (Fin 2) (Fin 2) L) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) L) 0 1 := by
    intro g
    simp [val_mul_apply, gl2Weyl_val]
  have hmul10 : ∀ g : GL (Fin 2) L, (((gl2Weyl * g : GL (Fin 2) L)) : Matrix (Fin 2) (Fin 2) L) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) L) 0 0 := by
    intro g
    simp [val_mul_apply, gl2Weyl_val]
  have e1 : ∀ g : GL (Fin 2) L, adelicWeyl (𝓞 L) L * (globalPoints (𝓞 L) L g * y) =
      globalPoints (𝓞 L) L (gl2Weyl * g * gl2Weyl) * (adelicWeyl (𝓞 L) L * y) := by
    intro g
    rw [hw, map_mul, map_mul]
    calc globalPoints (𝓞 L) L gl2Weyl * (globalPoints (𝓞 L) L g * y)
        = globalPoints (𝓞 L) L gl2Weyl * globalPoints (𝓞 L) L g * 1 * y := by group
      _ = globalPoints (𝓞 L) L gl2Weyl * globalPoints (𝓞 L) L g *
            (globalPoints (𝓞 L) L gl2Weyl * globalPoints (𝓞 L) L gl2Weyl) * y := by rw [hww]
      _ = _ := by group
  have hmul01 : ∀ g : GL (Fin 2) L, (((gl2Weyl * g : GL (Fin 2) L)) : Matrix (Fin 2) (Fin 2) L) 0 1 =
      (g : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    intro g
    simp [val_mul_apply, gl2Weyl_val]
  rcases hdich γ hγ with hΛ'γ | ⟨h00, h11, -⟩
  · left
    obtain ⟨⟨h10, h01⟩, -⟩ := (hΛ' γ).1 hΛ'γ
    refine ⟨NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero L γ h10 y, ?_⟩
    rw [e1 γ]
    exact NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero L _
      (by rw [hconj10]; exact h01) _
  · right

    have e2 : globalPoints (𝓞 L) L γ * y = adelicWeyl (𝓞 L) L * (globalPoints (𝓞 L) L (gl2Weyl * γ) * y) := by
      rw [hw, map_mul]
      calc globalPoints (𝓞 L) L γ * y = 1 * globalPoints (𝓞 L) L γ * y := by group
        _ = (globalPoints (𝓞 L) L gl2Weyl * globalPoints (𝓞 L) L gl2Weyl) * globalPoints (𝓞 L) L γ * y := by rw [hww]
        _ = _ := by group
    constructor
    · rw [e2, e1 (gl2Weyl * γ)]
      exact NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero L _
        (by rw [hconj10, hmul01]; exact h11) _
    · rw [e2, ← mul_assoc, hw, hww, one_mul]
      exact NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero L _ (by rw [hmul10]; exact h00) _

end Bracket

section Reindex

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

open scoped Classical in

theorem exists_refine_leftCosetRepresentatives
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ' : Subgroup (GL (Fin 2) L))
    (hΛ' : ∀ a : GL (Fin 2) L, a ∈ Λ' ↔ ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 0 / (a : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    {ι : Type} (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ) :
    ∃ T : Finset (GL (Fin 2) L), (↑T : Set (GL (Fin 2) L)) ⊆ Λ ∧
      T.card = (if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
        then 2 else 1) ∧
      ∀ γ : GL (Fin 2) L, ∃! p : ι × ↥T, (r p.1 * (p.2 : GL (Fin 2) L))⁻¹ * γ ∈ Λ' := by
  classical
  obtain ⟨hle, hdich, hex, hquot⟩ :=
    AutomorphicForm.mem_twistedStabilizer_iff_diagonal_or_antidiagonal K L σ hgen δ₀ hδ₀u hδ₀l hreg Λ hΛ Λ' hΛ'
  have hΛ'00 : ∀ a ∈ Λ', (a : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
    intro a ha h0
    obtain ⟨⟨h10, -⟩, -⟩ := (hΛ' a).1 ha
    have hdet : (a : Matrix (Fin 2) (Fin 2) L) 0 0 * (a : Matrix (Fin 2) (Fin 2) L) 1 1 -
        (a : Matrix (Fin 2) (Fin 2) L) 0 1 * (a : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 := by
      rw [← Matrix.det_fin_two, ← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    rw [h0, h10, zero_mul, mul_zero, sub_zero] at hdet
    exact hdet rfl
  by_cases hN : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
  · obtain ⟨γ₀, hγ₀Λ, h00, h11⟩ := hex hN
    have hγ₀1 : γ₀ ≠ 1 := by
      intro h; rw [h] at h00; simp at h00
    refine ⟨{1, γ₀}, ?_, ?_, ?_⟩
    · intro t ht
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · exact Λ.one_mem
      · exact hγ₀Λ
    · rw [if_pos hN, Finset.card_pair hγ₀1.symm]
    · intro γ
      obtain ⟨i, hi, hiu⟩ := hr γ
      have hmem1 : (1 : GL (Fin 2) L) ∈ ({1, γ₀} : Finset (GL (Fin 2) L)) := by simp
      have hmemγ : γ₀ ∈ ({1, γ₀} : Finset (GL (Fin 2) L)) := by simp
      have hfst : ∀ p : ι × ↥({1, γ₀} : Finset (GL (Fin 2) L)),
          (r p.1 * (p.2 : GL (Fin 2) L))⁻¹ * γ ∈ Λ' → p.1 = i := by
        rintro ⟨j, t⟩ h
        apply hiu j
        have ht : (t : GL (Fin 2) L) ∈ Λ := by
          have := t.2
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h1 | h1 <;> rw [h1]
          · exact Λ.one_mem
          · exact hγ₀Λ
        have : (r j)⁻¹ * γ = (t : GL (Fin 2) L) * ((r j * (t : GL (Fin 2) L))⁻¹ * γ) := by group
        rw [this]
        exact Λ.mul_mem ht (hle h)
      rcases hdich _ hi with hΛ'l | ⟨hl00, -, -⟩
      · refine ⟨(i, ⟨1, hmem1⟩), by show (r i * 1)⁻¹ * γ ∈ Λ'; rw [mul_one]; exact hΛ'l, ?_⟩
        rintro ⟨j, t⟩ h
        have hj := hfst ⟨j, t⟩ h
        subst hj
        have ht := t.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with h1 | h1
        · exact Prod.ext rfl (Subtype.ext h1)
        · exfalso
          have h' : (γ₀⁻¹ * ((r j)⁻¹ * γ)) ∈ Λ' := by
            have : (r j * (t : GL (Fin 2) L))⁻¹ * γ = γ₀⁻¹ * ((r j)⁻¹ * γ) := by rw [h1]; group
            rwa [this] at h
          have hinv : γ₀⁻¹ ∈ Λ' := by
            have := Λ'.mul_mem h' (Λ'.inv_mem hΛ'l)
            rwa [mul_inv_cancel_right] at this
          have hγ₀' : γ₀ ∈ Λ' := by
            have := Λ'.inv_mem hinv
            rwa [inv_inv] at this
          exact hΛ'00 _ hγ₀' h00
      · refine ⟨(i, ⟨γ₀, hmemγ⟩), ?_, ?_⟩
        · show (r i * γ₀)⁻¹ * γ ∈ Λ'
          have : (r i * γ₀)⁻¹ * γ = γ₀⁻¹ * ((r i)⁻¹ * γ) := by group
          rw [this]
          exact hquot γ₀ hγ₀Λ _ hi h00 hl00
        · rintro ⟨j, t⟩ h
          have hj := hfst ⟨j, t⟩ h
          subst hj
          have ht := t.2
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with h1 | h1
          · exfalso
            have h' : (r j)⁻¹ * γ ∈ Λ' := by
              have : (r j * (t : GL (Fin 2) L))⁻¹ * γ = (r j)⁻¹ * γ := by rw [h1]; group
              rwa [this] at h
            exact hΛ'00 _ h' hl00
          · exact Prod.ext rfl (Subtype.ext h1)
  · refine ⟨{1}, by simp [Λ.one_mem], by rw [if_neg hN, Finset.card_singleton], ?_⟩
    intro γ
    obtain ⟨i, hi, hiu⟩ := hr γ
    have hΛ'l : (r i)⁻¹ * γ ∈ Λ' := by
      rcases hdich _ hi with h | ⟨-, -, hN'⟩
      · exact h
      · exact absurd hN' hN
    refine ⟨(i, ⟨1, Finset.mem_singleton_self 1⟩), by show (r i * 1)⁻¹ * γ ∈ Λ'; rw [mul_one]; exact hΛ'l, ?_⟩
    rintro ⟨j, t⟩ h
    have ht : (t : GL (Fin 2) L) = 1 := Finset.mem_singleton.1 t.2
    have hj : j = i := by
      apply hiu j
      have : (r j)⁻¹ * γ = (r j * (t : GL (Fin 2) L))⁻¹ * γ := by rw [ht]; group
      rw [this]; exact hle h
    subst hj
    exact Prod.ext rfl (Subtype.ext ht)

theorem tsum_refine_eq_card_mul
    (Λ : Subgroup (GL (Fin 2) L)) {ι : Type} (r : ι → GL (Fin 2) L)
    (T : Finset (GL (Fin 2) L)) (hT : (↑T : Set (GL (Fin 2) L)) ⊆ Λ)
    (G : AdelicGL2 (𝓞 L) L → ℂ) (hG : ∀ γ ∈ Λ, ∀ y, G (globalPoints (𝓞 L) L γ * y) = G y)
    (x : AdelicGL2 (𝓞 L) L) (hsum : Summable fun i => G ((globalPoints (𝓞 L) L (r i))⁻¹ * x)) :
    ∑' p : ι × ↥T, G ((globalPoints (𝓞 L) L (r p.1 * (p.2 : GL (Fin 2) L)))⁻¹ * x) =
      (T.card : ℂ) * ∑' i, G ((globalPoints (𝓞 L) L (r i))⁻¹ * x) := by
  classical
  have hconst : ∀ p : ι × ↥T, G ((globalPoints (𝓞 L) L (r p.1 * (p.2 : GL (Fin 2) L)))⁻¹ * x) =
      G ((globalPoints (𝓞 L) L (r p.1))⁻¹ * x) := by
    rintro ⟨i, t⟩
    have ht : ((t : GL (Fin 2) L))⁻¹ ∈ Λ := Λ.inv_mem (hT t.2)
    show G ((globalPoints (𝓞 L) L (r i * (t : GL (Fin 2) L)))⁻¹ * x) = G ((globalPoints (𝓞 L) L (r i))⁻¹ * x)
    rw [map_mul, mul_inv_rev, ← map_inv, mul_assoc]
    exact hG _ ht _
  have hswap : ∑' p : ι × ↥T, G ((globalPoints (𝓞 L) L (r p.1 * (p.2 : GL (Fin 2) L)))⁻¹ * x) =
      ∑' p : ↥T × ι, G ((globalPoints (𝓞 L) L (r p.2))⁻¹ * x) := by
    rw [← Equiv.tsum_eq (Equiv.prodComm ↥T ι)]
    refine tsum_congr fun p => ?_
    rcases p with ⟨t, i⟩
    simpa using hconst ⟨i, t⟩

  set f : ι → ℂ := fun i => G ((globalPoints (𝓞 L) L (r i))⁻¹ * x) with hf
  set S : ℂ := ∑' i, f i with hS
  have hfS : HasSum f S := hsum.hasSum
  have hslice : ∀ t : ↥T, HasSum (fun p : ↥T × ι => if p.1 = t then f p.2 else 0) S := by
    intro t
    have hinj : Function.Injective (fun i : ι => (t, i)) := fun a b h => (Prod.ext_iff.1 h).2
    refine (hinj.hasSum_iff ?_).1 ?_
    · rintro ⟨t', i⟩ hp
      have h : t' ≠ t := by
        rintro rfl
        exact hp ⟨i, rfl⟩
      simp [h]
    · have : ((fun p : ↥T × ι => if p.1 = t then f p.2 else 0) ∘ fun i : ι => (t, i)) = f := by
        funext i; simp
      rw [this]; exact hfS
  have htot : HasSum (fun p : ↥T × ι => f p.2) ((Finset.univ : Finset ↥T).card • S) := by
    have h := hasSum_sum (s := (Finset.univ : Finset ↥T)) (fun t _ => hslice t)
    simp only [Finset.sum_const] at h
    convert h using 2 with p
    rw [Finset.sum_ite_eq]
    simp
  rw [hswap, htot.tsum_eq, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

end Reindex

end FDTB3

open AutomorphicForm in
set_option maxHeartbeats 4000000 in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
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
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))

    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ) :
    (∫⁻ x in Φ₀, ∑' i, ‖(1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) < ⊤ ∧
    IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => ∑' i,
        (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL)
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) := by
  classical
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ :=
    (NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box L L).1
  set gp := globalPoints (𝓞 L) L with hgp
  set μ : Measure (AdelicGL2 (𝓞 L) L) := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set Slab : Set (AdelicGL2 (𝓞 L) L) := {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hSlab
  set BR : Set (AdelicGL2 (𝓞 L) L) := {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} with hBR
  set BRw : Set (AdelicGL2 (𝓞 L) L) := {y : AdelicGL2 (𝓞 L) L |
      Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)} with hBRw
  set w : AdelicGL2 (𝓞 L) L := adelicWeyl (𝓞 L) L with hw
  set F : AdelicGL2 (𝓞 L) L → ℂ := FDTB3.orb νZL D σ ξL δ₀ φ with hF
  have hFdef : ∀ y, F y = ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      φ (y⁻¹ * gp δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) ∂νZL := fun y => rfl
  have hForb : ∀ y, F y = FDTOrbAbs.orb νZL D σ ξL δ₀ φ y := fun y => rfl
  set A : AdelicGL2 (𝓞 L) L → ENNReal := FDTOrbAbs.orbAbs D σ ξL νZL δ₀ φ with hA
  have hFA : ∀ y, ‖F y‖ₑ ≤ A y := fun y => FDTOrbAbs.enorm_orb_le_orbAbs D σ ξL νZL δ₀ φ y

  obtain ⟨H, hHc, hH, μH, hμH, hμHr⟩ :=
    AutomorphicForm.exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure K L D σ
  haveI := hμH
  haveI := hμHr

  have hdet : ∀ a : GL (Fin 2) L, (a : Matrix (Fin 2) (Fin 2) L) 0 0 * (a : Matrix (Fin 2) (Fin 2) L) 1 1 - (a : Matrix (Fin 2) (Fin 2) L) 0 1 * (a : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 := by
    intro a; rw [← Matrix.det_fin_two, ← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  have hvm : ∀ (x y : GL (Fin 2) L) (i j : Fin 2), ((x * y : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
      (x : Matrix (Fin 2) (Fin 2) L) i 0 * (y : Matrix (Fin 2) (Fin 2) L) 0 j + (x : Matrix (Fin 2) (Fin 2) L) i 1 * (y : Matrix (Fin 2) (Fin 2) L) 1 j := by
    intro x y i j; rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hinvd : ∀ a : GL (Fin 2) L, (a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Matrix (Fin 2) (Fin 2) L) 0 0)⁻¹ ∧ ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = ((a : Matrix (Fin 2) (Fin 2) L) 1 1)⁻¹ := by
    intro a h10 h01
    have h00 : (a : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
      have h := hdet a; rw [h10, mul_zero, sub_zero] at h; exact left_ne_zero_of_mul h
    have h11 : (a : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
      have h := hdet a; rw [h10, mul_zero, sub_zero] at h; exact right_ne_zero_of_mul h
    have e : ∀ i j, ((a⁻¹ * a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = if i = j then 1 else 0 := by
      intro i j; rw [inv_mul_cancel, Units.val_one, Matrix.one_apply]
    have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
    rw [hvm] at e00 e01 e10 e11
    simp only [h10, h01, mul_zero, add_zero, zero_add, if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false,
      Fin.zero_eq_one_iff] at e00 e01 e10 e11
    have i10 : ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := (mul_eq_zero.1 e10).resolve_right h00
    have i01 : ((a⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := (mul_eq_zero.1 e01).resolve_right h11
    exact ⟨i10, i01, eq_inv_of_mul_eq_one_left e00, eq_inv_of_mul_eq_one_left e11⟩
  let Λ₀ : Subgroup (GL (Fin 2) L) :=
    { carrier := {γ | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L)}
      mul_mem' := by
        rintro a b ⟨ha10, ha01, ⟨ka, hka⟩⟩ ⟨hb10, hb01, ⟨kb, hkb⟩⟩
        have ha11 : (a : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
          have h := hdet a; rw [ha10, mul_zero, sub_zero] at h; exact right_ne_zero_of_mul h
        have hb11 : (b : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
          have h := hdet b; rw [hb10, mul_zero, sub_zero] at h; exact right_ne_zero_of_mul h
        refine ⟨by rw [hvm, ha10, hb10, zero_mul, mul_zero, add_zero],
          by rw [hvm, ha01, hb01, mul_zero, zero_mul, add_zero], ⟨ka * kb, ?_⟩⟩
        rw [hvm, hvm, ha01, ha10, zero_mul, add_zero, zero_mul, zero_add, map_mul, hka, hkb]
        field_simp
      one_mem' := ⟨by simp, by simp, ⟨1, by simp⟩⟩
      inv_mem' := by
        rintro a ⟨ha10, ha01, ⟨ka, hka⟩⟩
        obtain ⟨i10, i01, i00, i11⟩ := hinvd a ha10 ha01
        have h00 : (a : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
          have h := hdet a; rw [ha10, mul_zero, sub_zero] at h; exact left_ne_zero_of_mul h
        have h11 : (a : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
          have h := hdet a; rw [ha10, mul_zero, sub_zero] at h; exact right_ne_zero_of_mul h
        refine ⟨i10, i01, ⟨ka⁻¹, ?_⟩⟩
        rw [i00, i11, map_inv₀, hka]
        field_simp }
  have hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L) := fun _ => Iff.rfl
  have hΛ₀' : ∀ a : GL (Fin 2) L, a ∈ Λ₀ ↔ ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      (a : Matrix (Fin 2) (Fin 2) L) 0 0 / (a : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L) := fun _ => and_assoc.symm
  obtain ⟨hΛ₀Λ, -, -, -⟩ :=
    AutomorphicForm.mem_twistedStabilizer_iff_diagonal_or_antidiagonal K L σ hgen δ₀ hδ₀u hδ₀l hreg Λ hΛ Λ₀ hΛ₀'
  obtain ⟨κ₀, hκ₀, Ω, hΩfd, hshell⟩ :=
    AutomorphicForm.exists_pos_isFundamentalDomain_forall_setIntegral_indicator_slab_bracket_eq_mul_of_sigmaCentraliser
      K L α β hα hαβ D σ hgen H hHc hH μH Λ₀ hΛ₀

  have hΛ₀H : Λ₀.map gp ≤ H := by
    intro h hh
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hh
    obtain ⟨ha10, ha01, ⟨k, hk⟩⟩ := (hΛ₀ a).1 ha
    obtain ⟨i10, i01, i00, i11⟩ := hinvd a ha10 ha01
    have h00 : (a : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
      have h := hdet a; rw [ha10, mul_zero, sub_zero] at h; exact left_ne_zero_of_mul h
    have h11 : (a : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
      have h := hdet a; rw [ha10, mul_zero, sub_zero] at h; exact right_ne_zero_of_mul h
    refine (hH _).2 ⟨?_, ?_, ?_⟩
    · show algebraMap L (AdeleRing (𝓞 L) L) ((a : Matrix (Fin 2) (Fin 2) L) 1 0) = 0
      rw [ha10, map_zero]
    · show algebraMap L (AdeleRing (𝓞 L) L) ((a : Matrix (Fin 2) (Fin 2) L) 0 1) = 0
      rw [ha01, map_zero]
    ·
      have hratio : σ ((a : Matrix (Fin 2) (Fin 2) L) 0 0) / (a : Matrix (Fin 2) (Fin 2) L) 0 0 = σ ((a : Matrix (Fin 2) (Fin 2) L) 1 1) / (a : Matrix (Fin 2) (Fin 2) L) 1 1 := by
        have e : (a : Matrix (Fin 2) (Fin 2) L) 0 0 = algebraMap K L k * (a : Matrix (Fin 2) (Fin 2) L) 1 1 := by
          rw [hk]; field_simp
        rw [e, map_mul, AlgEquiv.commutes]
        have : σ ((a : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := (map_ne_zero σ).2 h11
        have hk0 : algebraMap K L k ≠ 0 := by
          intro h0; apply h00; rw [e, h0, zero_mul]
        field_simp
      set ζ : Lˣ := Units.mk0 (σ ((a : Matrix (Fin 2) (Fin 2) L) 1 1) / (a : Matrix (Fin 2) (Fin 2) L) 1 1)
        (div_ne_zero ((map_ne_zero σ).2 h11) h11) with hζ
      have hmat : Matrix.GeneralLinearGroup.map (σ : L →+* L) a * a⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) ζ := by
        refine Matrix.GeneralLinearGroup.ext fun i j => ?_
        have hmap : ∀ i j, ((Matrix.GeneralLinearGroup.map (σ : L →+* L) a : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = σ ((a : Matrix (Fin 2) (Fin 2) L) i j) :=
          fun i j => rfl
        rw [hvm, hmap, hmap]
        fin_cases i <;> fin_cases j
        · simp [ha01, i10, i00, Matrix.GeneralLinearGroup.scalar, hζ]
          simpa [div_eq_mul_inv] using hratio
        · simp [ha01, i01, i11, Matrix.GeneralLinearGroup.scalar, hζ]
        · simp [ha10, i00, i10, Matrix.GeneralLinearGroup.scalar, hζ]
        · simp [ha10, i01, i11, Matrix.GeneralLinearGroup.scalar, hζ, div_eq_mul_inv]
      have L2 : sigmaAdelicAct K L D σ (gp a) = gp (Matrix.GeneralLinearGroup.map (σ : L →+* L) a) :=
        AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ a
      rw [L2, ← map_inv, ← map_mul, hmat, hgp, FDTB3.globalPoints_scalar, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩

  obtain ⟨T, hTΛ, hTcard, hr'⟩ :=
    FDTB3.exists_refine_leftCosetRepresentatives K L σ hgen δ₀ hδ₀u hδ₀l hreg Λ hΛ Λ₀ hΛ₀' r hr
  haveI : Countable (ι × ↥T) := inferInstance
  set r' : ι × ↥T → GL (Fin 2) L := fun p => r p.1 * (p.2 : GL (Fin 2) L) with hr'def
  have hTpos : 0 < T.card := by rw [hTcard]; split_ifs <;> norm_num
  obtain ⟨t₀, ht₀⟩ := Finset.card_pos.1 hTpos

  set bR : AdelicGL2 (𝓞 L) L → ℂ := fun u => (1 : ℂ) - Set.indicator BR (fun _ => (1 : ℂ)) u - Set.indicator BRw (fun _ => (1 : ℂ)) u with hbR
  set G : AdelicGL2 (𝓞 L) L → ℂ := fun y => bR y * F y with hG
  set g : AdelicGL2 (𝓞 L) L → ENNReal := fun y => ‖G y‖ₑ with hg
  have hBRmem : ∀ u, u ∈ BR ↔ Real.exp R < NumberField.AdelicHeight.adelicHeight L u := fun u => Iff.rfl
  have hBRwmem : ∀ u, u ∈ BRw ↔ Real.exp R < NumberField.AdelicHeight.adelicHeight L (w * u) := fun u => Iff.rfl
  have hInd : ∀ (S₁ S₂ : Set (AdelicGL2 (𝓞 L) L)) (u v : AdelicGL2 (𝓞 L) L), (u ∈ S₁ ↔ v ∈ S₂) →
      S₁.indicator (fun _ => (1 : ℂ)) u = S₂.indicator (fun _ => (1 : ℂ)) v := by
    intro S₁ S₂ u v h
    by_cases hu : u ∈ S₁
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (h.1 hu)]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (fun hv => hu (h.2 hv))]
  have hFΛ : ∀ γ ∈ Λ, ∀ y, F (gp γ * y) = F y := fun γ hγ y =>
    FDTB3.orb_globalPoints_mul_of_mem νZL D σ ξL hξt δ₀ φ Λ hΛ γ hγ y
  have hGΛ : ∀ γ ∈ Λ, ∀ y, G (gp γ * y) = G y := by
    intro γ hγ y
    simp only [hG, hbR]
    rw [hFΛ γ hγ y]
    congr 1
    rcases FDTB3.adelicHeight_globalPoints_mul_dichotomy K L σ hgen δ₀ hδ₀u hδ₀l hreg Λ hΛ Λ₀ hΛ₀' γ hγ y with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hInd BR BR (gp γ * y) y (by rw [hBRmem, hBRmem, h1]),
        hInd BRw BRw (gp γ * y) y (by rw [hBRwmem, hBRwmem, h2])]
    · rw [hInd BR BRw (gp γ * y) y (by rw [hBRmem, hBRwmem, h1]),
        hInd BRw BR (gp γ * y) y (by rw [hBRwmem, hBRmem, h2])]
      ring
  have hgΛ₀ : ∀ γ ∈ Λ₀, ∀ y, g (gp γ * y) = g y := fun γ hγ y => by
    simp only [hg]; rw [hGΛ γ (hΛ₀Λ hγ) y]

  have hHtc : Continuous (NumberField.AdelicHeight.adelicHeight L) := NumberField.AdelicHeight.continuous_adelicHeight L
  have hBRm : MeasurableSet BR := measurableSet_lt measurable_const hHtc.measurable
  have hBRwm : MeasurableSet BRw := measurableSet_lt measurable_const (hHtc.comp (continuous_const.mul continuous_id)).measurable
  have hSlabm : MeasurableSet Slab := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc L α β
  have hcc : Continuous (centralScalar (𝓞 L) L) := FDTOrbAbs.continuous_centralScalar
  have hIc : Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ((ξL ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) *
        φ (p.1⁻¹ * gp δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L p.2 * p.1)) :=
    (hξc.comp continuous_snd).mul (hφc.comp (((continuous_fst.inv).mul continuous_const).mul
      ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp ((hcc.comp continuous_snd).mul continuous_fst))))
  have hFm : Measurable F := by
    have : F = fun y => ∫ z, (fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ((ξL ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) *
        φ (p.1⁻¹ * gp δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L p.2 * p.1))) (y, z) ∂νZL := rfl
    rw [this]
    exact (hIc.stronglyMeasurable.integral_prod_right' (ν := νZL)).measurable
  have hbRm : Measurable bR :=
    (measurable_const.sub (measurable_const.indicator hBRm)).sub (measurable_const.indicator hBRwm)
  have hGm : Measurable G := hbRm.mul hFm
  have hgm : Measurable g := hGm.enorm

  have hΦ₀' : IsFundamentalDomain ((⊤ : Subgroup (GL (Fin 2) L)).map gp) Φ₀ (μ.restrict Slab) := by
    rw [← MonoidHom.range_eq_map]; exact hΦ₀
  have hrΓ : ∀ p : ι × ↥T, r' p ∈ (⊤ : Subgroup (GL (Fin 2) L)) := fun _ => Subgroup.mem_top _
  have hr'' : ∀ γ ∈ (⊤ : Subgroup (GL (Fin 2) L)), ∃! p : ι × ↥T, (r' p)⁻¹ * γ ∈ Λ₀ := fun γ _ => hr' γ
  have hS' : ∀ γ ∈ (⊤ : Subgroup (GL (Fin 2) L)), ∀ x : AdelicGL2 (𝓞 L) L, gp γ * x ∈ Slab ↔ x ∈ Slab := by
    intro γ _ x
    simp only [hSlab, hgp, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
      AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  have hLINT := AutomorphicForm.setLIntegral_tsum_comp_globalPoints_inv_mul_eq_lintegral_haarQuotient_setLIntegral_of_subgroup
    L ⊤ Slab hSlabm hS' Φ₀ hΦ₀s hΦ₀' Λ₀ le_top r' hrΓ hr'' H hHc hΛ₀H μH Ω hΩfd g hgm hgΛ₀
  have hgT : ∀ (i : ι) (x : AdelicGL2 (𝓞 L) L), g ((gp (r' (i, ⟨t₀, ht₀⟩)))⁻¹ * x) = g ((gp (r i))⁻¹ * x) := by
    intro i x
    have ht : ((t₀ : GL (Fin 2) L))⁻¹ ∈ Λ := Λ.inv_mem (hTΛ ht₀)
    show g ((gp (r i * t₀))⁻¹ * x) = g ((gp (r i))⁻¹ * x)
    rw [map_mul, mul_inv_rev, ← map_inv, mul_assoc]
    simp only [hg]; rw [hGΛ _ ht _]
  have hdom : ∫⁻ x in Φ₀, ∑' i, g ((gp (r i))⁻¹ * x) ∂μ ≤ ∫⁻ x in Φ₀, ∑' p : ι × ↥T, g ((gp (r' p))⁻¹ * x) ∂μ := by
    refine lintegral_mono fun x => ?_
    have hinj : Function.Injective (fun i : ι => ((i, ⟨t₀, ht₀⟩) : ι × ↥T)) := fun a b h => (Prod.ext_iff.1 h).1
    calc ∑' i, g ((gp (r i))⁻¹ * x) = ∑' i, g ((gp (r' (i, ⟨t₀, ht₀⟩)))⁻¹ * x) := tsum_congr fun i => (hgT i x).symm
      _ ≤ ∑' p : ι × ↥T, g ((gp (r' p))⁻¹ * x) :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj (fun p : ι × ↥T => g ((gp (r' p))⁻¹ * x))

  have hFH : ∀ (h : ↥H) (y : AdelicGL2 (𝓞 L) L), ‖F ((h : AdelicGL2 (𝓞 L) L) * y)‖ₑ = ‖F y‖ₑ := by
    intro h y
    obtain ⟨h10, h01, hcen⟩ := (hH h).1 h.2
    rw [← ofReal_norm, ← ofReal_norm]
    exact congrArg ENNReal.ofReal
      (FDTOrbAbs.norm_orb_mul_of_diag_of_mem_center D σ ξL hξc hξt νZL δ₀ φ hδ₀u hδ₀l _ h10 h01 hcen y)
  have hfib : ∀ (h : ↥H) (y : AdelicGL2 (𝓞 L) L), Slab.indicator g ((h : AdelicGL2 (𝓞 L) L) * y) =
      ‖Set.indicator Slab (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) * bR ((h : AdelicGL2 (𝓞 L) L) * y)‖ₑ * ‖F y‖ₑ := by
    intro h y
    by_cases hm : (h : AdelicGL2 (𝓞 L) L) * y ∈ Slab
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, one_mul]
      simp only [hg, hG]
      rw [enorm_mul, hFH]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul, enorm_zero, zero_mul]
  have hinner : ∀ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
      ∫⁻ h in Ω, Slab.indicator g ((h : AdelicGL2 (𝓞 L) L) * q.out) ∂μH =
        ENNReal.ofReal (κ₀ * |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L q.out)
            - Real.log (NumberField.AdelicHeight.adelicHeight L (w * q.out))|) * ‖F q.out‖ₑ := by
    intro q
    simp_rw [hfib]
    rw [lintegral_mul_const _ ?_, (hshell q.out R).1]
    exact ((((measurable_const.indicator hSlabm).mul hbRm).comp
      (measurable_subtype_coe.mul_const _)).enorm)

  obtain ⟨-, hA1, -, hA3, -, -⟩ :=
    AutomorphicForm.lintegral_abs_twistedOrbital_lt_top_and_integrable_norm_and_weighted_and_exists_height_mul_le_of_zpowers
      K L νZL ΩL hΩL D σ hgen ξL hξc hξt δ₀ hδ₀u hδ₀l hreg I hI Λ hΛ r hr H hHc hH μH φ hφc hφs
  set νQ := HaarQuotient.measure μ H μH with hνQ
  have hA1' : ∫⁻ q, A q.out ∂νQ < ⊤ := hA1
  have hA3' : ∫⁻ q, ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
      - Real.log (NumberField.AdelicHeight.adelicHeight L (w * (q.out : AdelicGL2 (𝓞 L) L))))| * A q.out ∂νQ < ⊤ := hA3

  have hAm : Measurable A := by
    rw [hA]; unfold FDTOrbAbs.orbAbs
    exact Measurable.lintegral_prod_right ((hξc.comp continuous_snd).measurable.enorm.mul
      ((hφc.comp (((continuous_fst.inv).mul continuous_const).mul
        ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp ((hcc.comp continuous_snd).mul continuous_fst)))).measurable.enorm))
  haveI : MeasurableMul (AdeleRing (𝓞 L) L)ˣ := by infer_instance
  have hAinv : ∀ h ∈ H, ∀ y, A (h * y) = A y := by
    intro h hh y
    obtain ⟨h10, h01, hcen⟩ := (hH h).1 hh
    exact FDTOrbAbs.orbAbs_mul_of_diag_of_mem_center D σ ξL hξc hξt νZL δ₀ φ hδ₀u hδ₀l h h10 h01 hcen y
  have hAQ : Measurable fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => A q.out := by
    rw [measurable_from_quotient]
    have hcomp : ((fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => A q.out) ∘ Quotient.mk'') = A := by
      funext y
      have h1 : (MulAction.orbitRel H (AdelicGL2 (𝓞 L) L))
          ((Quotient.mk'' y : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L)).out) y := Quotient.mk_out y
      rw [MulAction.orbitRel_apply] at h1
      obtain ⟨h, hh⟩ := h1
      simp only [Function.comp_apply]
      rw [← hh]
      exact hAinv _ h.2 y
    rw [hcomp]; exact hAm
  have hbound : ∀ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
      ENNReal.ofReal (κ₀ * |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L q.out)
            - Real.log (NumberField.AdelicHeight.adelicHeight L (w * q.out))|) * ‖F q.out‖ₑ ≤
        ENNReal.ofReal (κ₀ * (2 * |R|)) * A q.out +
          ENNReal.ofReal κ₀ * (ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
            - Real.log (NumberField.AdelicHeight.adelicHeight L (w * (q.out : AdelicGL2 (𝓞 L) L))))| * A q.out) := by
    intro q
    set a := Real.log (NumberField.AdelicHeight.adelicHeight L q.out) with ha
    set b := Real.log (NumberField.AdelicHeight.adelicHeight L (w * q.out)) with hb
    have htri : |2 * R - a - b| ≤ 2 * |R| + |(-a - b)| := by
      have : 2 * R - a - b = 2 * R + (-a - b) := by ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two]
    have hk : ENNReal.ofReal (κ₀ * |2 * R - a - b|) ≤ ENNReal.ofReal (κ₀ * (2 * |R|)) + ENNReal.ofReal κ₀ * ENNReal.ofReal |(-a - b)| := by
      rw [← ENNReal.ofReal_mul hκ₀.le, ← ENNReal.ofReal_add (by positivity) (by positivity), ← mul_add]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left htri hκ₀.le)
    calc ENNReal.ofReal (κ₀ * |2 * R - a - b|) * ‖F q.out‖ₑ
        ≤ (ENNReal.ofReal (κ₀ * (2 * |R|)) + ENNReal.ofReal κ₀ * ENNReal.ofReal |(-a - b)|) * A q.out :=
          mul_le_mul' hk (hFA _)
      _ = _ := by ring
  have hI : ∫⁻ x in Φ₀, ∑' i, g ((gp (r i))⁻¹ * x) ∂μ < ⊤ := by
    refine lt_of_le_of_lt hdom ?_
    rw [hLINT]
    simp_rw [hinner]
    refine lt_of_le_of_lt (lintegral_mono hbound) ?_
    rw [lintegral_add_left ((hAQ.const_mul _)), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA1',
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA3'⟩
  have hmeas_i : ∀ i, Measurable fun x : AdelicGL2 (𝓞 L) L => G ((gp (r i))⁻¹ * x) :=
    fun i => hGm.comp (measurable_const_mul _)
  have hSumm : ∀ᵐ x ∂μ.restrict Φ₀, Summable fun i => ‖G ((gp (r i))⁻¹ * x)‖ := by
    have hlt : ∀ᵐ x ∂μ.restrict Φ₀, ∑' i, g ((gp (r i))⁻¹ * x) < ⊤ :=
      ae_lt_top (Measurable.ennreal_tsum fun i => (hmeas_i i).enorm) hI.ne
    filter_upwards [hlt] with x hx
    have hne : ∑' i, ((‖G ((gp (r i))⁻¹ * x)‖₊ : NNReal) : ENNReal) ≠ ⊤ := by
      have : (fun i => ((‖G ((gp (r i))⁻¹ * x)‖₊ : NNReal) : ENNReal)) = fun i => g ((gp (r i))⁻¹ * x) := by
        funext i; simp only [hg, enorm_eq_nnnorm]
      rw [this]; exact hx.ne
    have hs := ENNReal.tsum_coe_ne_top_iff_summable.1 hne
    simpa using NNReal.summable_coe.2 hs
  refine ⟨?_, ?_⟩
  · show ∫⁻ x in Φ₀, ∑' i, g ((gp (r i))⁻¹ * x) ∂μ < ⊤
    exact hI
  · show IntegrableOn (fun x => ∑' i, G ((gp (r i))⁻¹ * x)) Φ₀ μ
    refine ⟨?_, ?_⟩
    · exact aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
        (f := fun s x => ∑ i ∈ s, G ((gp (r i))⁻¹ * x))
        (fun s => (Finset.measurable_sum s fun i _ => hmeas_i i).aestronglyMeasurable)
        (by filter_upwards [hSumm] with x hx; exact hx.of_norm.hasSum)
    · show ∫⁻ x in Φ₀, ‖∑' i, G ((gp (r i))⁻¹ * x)‖ₑ ∂μ < ⊤
      refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hI
      exact enorm_tsum_le_tsum_enorm

end

end S_AutomorphicForm_setLIntegral_tsum_norm_bracket_mul_twistedOrbital_lt_top_and_integrableOn
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_tsum_norm_bracket_mul_twistedOrbital_lt_top_and_integrableOn (solution)
