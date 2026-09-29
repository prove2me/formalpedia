-- Prove2me | solution 1 for AutomorphicForm.exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/218281d9-2aa2-5ddd-84a3-ade4d7eb9908

import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.AutomorphicForm Topology"
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "mem_borelSubgroup_iff borelDiagFst borelDiagSnd adelicBorel AdelicGL2 centralScalar unipotentGL2 unipotentGL2_coe"
p2m_open "AutomorphicForm"

namespace BorelCoord

variable (K : Type) [Field K] [NumberField K]

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

def psiG (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) : AdelicGL2 (𝓞 K) K :=
  unipotentGL2 p.1 * centralScalar (𝓞 K) K p.2.1 * diagOne p.2.2

theorem psiG_apply (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) (i j : Fin 2) :
    ((psiG K p : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      !![(p.2.1 : AdeleRing (𝓞 K) K) * p.2.2, p.1 * p.2.1; 0, (p.2.1 : AdeleRing (𝓞 K) K)] i j := by
  rw [psiG, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  change (!![1, p.1; 0, 1] * Matrix.scalar (Fin 2) (p.2.1 : AdeleRing (𝓞 K) K) *
    Matrix.diagonal ![(p.2.2 : AdeleRing (𝓞 K) K), 1]) i j = _
  rw [Matrix.scalar_apply, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem psiG_mem (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    psiG K p ∈ adelicBorel (𝓞 K) K := by
  rw [mem_borelSubgroup_iff, psiG_apply]; rfl

theorem continuous_psiG : Continuous (psiG K) :=
  (((continuous_unipotentGL2 K).comp continuous_fst).mul
    ((continuous_centralScalar K).comp (continuous_fst.comp continuous_snd))).mul
    ((continuous_diagOne K).comp (continuous_snd.comp continuous_snd))

def psi (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) : adelicBorel (𝓞 K) K :=
  ⟨psiG K p, psiG_mem K p⟩

theorem continuous_psi : Continuous (psi K) := (continuous_psiG K).subtype_mk _

def theta (b : adelicBorel (𝓞 K) K) : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ :=
  (((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 * ((borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 K) K)ˣ),
    borelDiagSnd b, borelDiagFst b * (borelDiagSnd b)⁻¹)

theorem continuous_borelDiagSnd : Continuous (borelDiagSnd : adelicBorel (𝓞 K) K → (AdeleRing (𝓞 K) K)ˣ) := by
  have hent : ∀ i j : Fin 2, Continuous fun b : adelicBorel (𝓞 K) K =>
      (((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) := fun i j =>
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j).comp continuous_subtype_val
  refine Units.continuous_iff.mpr ⟨hent 1 1, ?_⟩
  simp_rw [← map_inv]
  exact (hent 1 1).comp continuous_inv

theorem continuous_borelDiagFst : Continuous (borelDiagFst : adelicBorel (𝓞 K) K → (AdeleRing (𝓞 K) K)ˣ) := by
  have hent : ∀ i j : Fin 2, Continuous fun b : adelicBorel (𝓞 K) K =>
      (((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) := fun i j =>
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem i j).comp continuous_subtype_val
  refine Units.continuous_iff.mpr ⟨hent 0 0, ?_⟩
  simp_rw [← map_inv]
  exact (hent 0 0).comp continuous_inv

theorem continuous_theta : Continuous (theta K) := by
  have h01 : Continuous fun b : adelicBorel (𝓞 K) K =>
      (((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) :=
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 0 1).comp continuous_subtype_val
  refine (h01.mul (Units.continuous_val.comp ((continuous_borelDiagSnd K).inv))).prodMk
    ((continuous_borelDiagSnd K).prodMk ((continuous_borelDiagFst K).mul (continuous_borelDiagSnd K).inv))

theorem theta_psi (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) : theta K (psi K p) = p := by
  obtain ⟨x, u, t⟩ := p
  have hsnd : borelDiagSnd (psi K (x, u, t)) = u := Units.ext (by
    change ((psiG K (x, u, t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = (u : AdeleRing (𝓞 K) K)
    rw [psiG_apply]; rfl)
  have hfst : borelDiagFst (psi K (x, u, t)) = u * t := Units.ext (by
    change ((psiG K (x, u, t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 =
      (u : AdeleRing (𝓞 K) K) * t
    rw [psiG_apply]; rfl)
  simp only [theta, hsnd, hfst]
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · change ((psiG K (x, u, t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 * _ = x
    rw [psiG_apply]
    change x * (u : AdeleRing (𝓞 K) K) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = x
    rw [mul_assoc, Units.mul_inv, mul_one]
  · change u * t * u⁻¹ = t
    rw [mul_comm u t, mul_inv_cancel_right]

theorem psi_theta (b : adelicBorel (𝓞 K) K) : psi K (theta K b) = b := by
  have h10 : (((b : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := b.2
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change ((psiG K (theta K b) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j = _
  rw [psiG_apply]
  set M := (((b : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) with hM
  have hu : ((borelDiagSnd b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = M 1 1 := rfl
  have ht : ((borelDiagFst b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = M 0 0 := rfl
  have hinv : M 1 1 * (((borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = 1 := by rw [← hu, Units.mul_inv]
  have e00 : ((borelDiagSnd b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
      ((borelDiagFst b * (borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = M 0 0 := by
    rw [Units.val_mul, hu, ht, mul_left_comm, hinv, mul_one]
  have e01 : M 0 1 * (((borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
      ((borelDiagSnd b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = M 0 1 := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  simp only [theta]
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact h10.symm
  · exact hu

def psiHomeo : (AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) ≃ₜ adelicBorel (𝓞 K) K where
  toFun := psi K
  invFun := theta K
  left_inv := theta_psi K
  right_inv := psi_theta K
  continuous_toFun := continuous_psi K
  continuous_invFun := continuous_theta K

def lmul (p q : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ :=
  (p.1 + (p.2.2 : AdeleRing (𝓞 K) K) * q.1, p.2.1 * q.2.1, p.2.2 * q.2.2)

theorem psi_mul (p q : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    psi K p * psi K q = psi K (lmul K p q) := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change (((psiG K p : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) *
      ((psiG K q : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) i j =
    ((psiG K (lmul K p q) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, psiG_apply, psiG_apply, psiG_apply, psiG_apply, psiG_apply]
  simp only [lmul, Units.val_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

def dens (t : (AdeleRing (𝓞 K) K)ˣ) : ℝ≥0∞ := ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)

theorem continuous_dens : Continuous (dens K) := by
  unfold dens
  refine ENNReal.continuous_ofReal.comp ?_
  exact (NumberField.TateGlobal.continuous_ideleNorm K).inv₀ fun t => (NumberField.TateGlobal.ideleNorm_pos t).ne'

theorem measurable_dens : Measurable (dens K) := (continuous_dens K).measurable

theorem dens_pos (t : (AdeleRing (𝓞 K) K)ˣ) : 0 < dens K t :=
  ENNReal.ofReal_pos.mpr (inv_pos.mpr (NumberField.TateGlobal.ideleNorm_pos t))

theorem dens_mul (t₀ t : (AdeleRing (𝓞 K) K)ˣ) :
    dens K (t₀⁻¹ * t) = (distribHaarChar (AdeleRing (𝓞 K) K) t₀ : ℝ≥0∞) * dens K t := by
  unfold dens NumberField.TateGlobal.ideleNorm
  rw [map_mul, map_inv, NNReal.coe_mul, mul_inv, NNReal.coe_inv, inv_inv,
    ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]

def idelicHaarW : Measure (AdeleRing (𝓞 K) K)ˣ := (NumberField.Idele.idelicHaar K).withDensity (dens K)

def rho : Measure (AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :=
  (adelicAddHaar (𝓞 K) K).prod ((NumberField.Idele.idelicHaar K).prod (idelicHaarW K))

def kappa : Measure (adelicBorel (𝓞 K) K) := (rho K).map (psi K)

scoped instance : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K

scoped instance secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

scoped instance secondCountableTopology_borel : SecondCountableTopology (adelicBorel (𝓞 K) K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

theorem isClosed_adelicBorel : IsClosed (adelicBorel (𝓞 K) K : Set (AdelicGL2 (𝓞 K) K)) := by
  have : (adelicBorel (𝓞 K) K : Set (AdelicGL2 (𝓞 K) K)) =
      (fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0) ⁻¹' {0} := by
    ext g; exact mem_borelSubgroup_iff _
  rw [this]
  exact isClosed_singleton.preimage ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).matrix_elem 1 0)

scoped instance locallyCompactSpace_borel : LocallyCompactSpace (adelicBorel (𝓞 K) K) := (isClosed_adelicBorel K).locallyCompactSpace

scoped instance sigmaFinite_adelicAddHaar : SigmaFinite (adelicAddHaar (𝓞 K) K) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  infer_instance

scoped instance locallyCompactSpace_idele : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance sigmaCompactSpace_idele : SigmaCompactSpace (AdeleRing (𝓞 K) K)ˣ :=
  @sigmaCompactSpace_of_locallyCompact_secondCountable _ _ (locallyCompactSpace_idele K) (secondCountableTopology_idele K)

scoped instance sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar K) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  infer_instance

scoped instance sFinite_idelicHaarW : SFinite (idelicHaarW K) := by unfold idelicHaarW; infer_instance

scoped instance sFinite_rho : SFinite (rho K) := by unfold rho; infer_instance

theorem map_mul_left_adelicAddHaar (x₀ : AdeleRing (𝓞 K) K) (t₀ : (AdeleRing (𝓞 K) K)ˣ) :
    (adelicAddHaar (𝓞 K) K).map (fun x => x₀ + (t₀ : AdeleRing (𝓞 K) K) * x) =
      (((distribHaarChar (AdeleRing (𝓞 K) K) t₀)⁻¹ : ℝ≥0) : ℝ≥0∞) • adelicAddHaar (𝓞 K) K := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  haveI : (adelicAddHaar (𝓞 K) K).Regular := by
    unfold adelicAddHaar Measure.addHaar; infer_instance
  have h1 : (adelicAddHaar (𝓞 K) K).map (fun x => (t₀ : AdeleRing (𝓞 K) K) * x) =
      (((distribHaarChar (AdeleRing (𝓞 K) K) t₀)⁻¹ : ℝ≥0) : ℝ≥0∞) • adelicAddHaar (𝓞 K) K := by
    refine Measure.ext fun s hs => ?_
    open scoped Pointwise in
    rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul,
      show (fun y => (t₀ : AdeleRing (𝓞 K) K) * y) ⁻¹' s = t₀⁻¹ • s from Set.preimage_smul t₀ s,
      ← distribHaarChar_mul (adelicAddHaar (𝓞 K) K) t₀⁻¹ s, map_inv]
  have hcomp : (fun x => x₀ + (t₀ : AdeleRing (𝓞 K) K) * x) =
      (fun x => x₀ + x) ∘ (fun x => (t₀ : AdeleRing (𝓞 K) K) * x) := rfl
  rw [hcomp, ← Measure.map_map (measurable_const_add x₀) (measurable_const_mul _), h1, Measure.map_smul,
    map_add_left_eq_self]

theorem map_mul_left_idelicHaarW (t₀ : (AdeleRing (𝓞 K) K)ˣ) :
    (idelicHaarW K).map (fun t => t₀ * t) = (distribHaarChar (AdeleRing (𝓞 K) K) t₀ : ℝ≥0∞) • idelicHaarW K := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul, idelicHaarW,
    withDensity_apply _ (measurable_const_mul _ hs), withDensity_apply _ hs]

  have h := lintegral_mul_left_eq_self (μ := NumberField.Idele.idelicHaar K)
    (fun t => s.indicator (dens K ∘ fun t => t₀⁻¹ * t) t) t₀
  have hind : ∀ t, s.indicator (dens K ∘ fun t => t₀⁻¹ * t) (t₀ * t) =
      ((fun t => t₀ * t) ⁻¹' s).indicator (dens K) t := by
    intro t
    simp only [Set.indicator, Set.mem_preimage, Function.comp_apply, inv_mul_cancel_left]
    rfl
  simp_rw [hind] at h
  rw [← lintegral_indicator (measurable_const_mul _ hs), h, ← lintegral_indicator hs]
  have : ∀ t, s.indicator (dens K ∘ fun t => t₀⁻¹ * t) t =
      (distribHaarChar (AdeleRing (𝓞 K) K) t₀ : ℝ≥0∞) * s.indicator (dens K) t := by
    intro t
    simp only [Set.indicator, Function.comp_apply, dens_mul]
    split_ifs <;> simp
  simp_rw [this]
  rw [lintegral_const_mul _ ((measurable_dens K).indicator hs)]

theorem map_lmul_rho (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) :
    (rho K).map (lmul K p) = rho K := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  obtain ⟨x₀, u₀, t₀⟩ := p
  have hl : lmul K (x₀, u₀, t₀) = Prod.map (fun x => x₀ + (t₀ : AdeleRing (𝓞 K) K) * x)
      (Prod.map (fun u => u₀ * u) (fun t => t₀ * t)) := rfl
  have hmx : Measurable (fun x : AdeleRing (𝓞 K) K => x₀ + (t₀ : AdeleRing (𝓞 K) K) * x) :=
    (measurable_const_add x₀).comp (measurable_const_mul _)
  have hmu : Measurable (fun u : (AdeleRing (𝓞 K) K)ˣ => u₀ * u) := measurable_const_mul u₀
  have hmt : Measurable (fun t : (AdeleRing (𝓞 K) K)ˣ => t₀ * t) := measurable_const_mul t₀
  rw [hl, rho, ← Measure.map_prod_map _ _ hmx (hmu.prodMap hmt), ← Measure.map_prod_map _ _ hmu hmt,
    map_mul_left_adelicAddHaar, map_mul_left_eq_self, map_mul_left_idelicHaarW, Measure.prod_smul_right,
    Measure.prod_smul_right, Measure.prod_smul_left, smul_smul, ← ENNReal.coe_mul, mul_inv_cancel₀ (distribHaarChar_pos).ne', ENNReal.coe_one, one_smul]

theorem continuous_lmul (p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) : Continuous (lmul K p) := by
  unfold lmul
  exact (continuous_const.add (continuous_const.mul continuous_fst)).prodMk
    ((continuous_const.mul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_const.mul (continuous_snd.comp continuous_snd)))

scoped instance isMulLeftInvariant_kappa : (kappa K).IsMulLeftInvariant := by
  refine ⟨fun b₀ => ?_⟩
  obtain ⟨p₀, rfl⟩ : ∃ p₀, psi K p₀ = b₀ := ⟨theta K b₀, psi_theta K b₀⟩
  rw [kappa, Measure.map_map (measurable_const_mul _) (continuous_psi K).measurable]
  have : (fun b => psi K p₀ * b) ∘ psi K = psi K ∘ lmul K p₀ := funext fun q => psi_mul K p₀ q
  rw [this, ← Measure.map_map (continuous_psi K).measurable, map_lmul_rho]
  exact (continuous_lmul K p₀).measurable

scoped instance isFiniteMeasureOnCompacts_idelicHaarW : IsFiniteMeasureOnCompacts (idelicHaarW K) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  refine ⟨fun C hC => ?_⟩
  rw [idelicHaarW, withDensity_apply _ hC.measurableSet]
  rcases C.eq_empty_or_nonempty with h | h
  · simp [h]
  obtain ⟨t₁, _, ht₁⟩ := hC.exists_isMaxOn h (continuous_dens K).continuousOn
  calc ∫⁻ t in C, dens K t ∂(NumberField.Idele.idelicHaar K)
      ≤ ∫⁻ _ in C, dens K t₁ ∂(NumberField.Idele.idelicHaar K) := setLIntegral_mono measurable_const fun t ht => ht₁ ht
    _ = dens K t₁ * (NumberField.Idele.idelicHaar K) C := setLIntegral_const C _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

scoped instance isFiniteMeasureOnCompacts_rho : IsFiniteMeasureOnCompacts (rho K) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  unfold rho; infer_instance

scoped instance isFiniteMeasureOnCompacts_kappa : IsFiniteMeasureOnCompacts (kappa K) := by
  refine ⟨fun C hC => ?_⟩
  rw [kappa, Measure.map_apply (continuous_psi K).measurable hC.measurableSet]
  exact ((psiHomeo K).isCompact_preimage.mpr hC).measure_lt_top

theorem idelicHaarW_univ_ne_zero : idelicHaarW K Set.univ ≠ 0 := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  rw [idelicHaarW, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  intro h
  rw [lintegral_eq_zero_iff (measurable_dens K)] at h
  have h2 : (NumberField.Idele.idelicHaar K) Set.univ = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    exact h.mono fun t ht htU => (dens_pos K t).ne' ht
  exact isOpen_univ.measure_ne_zero (NumberField.Idele.idelicHaar K) Set.univ_nonempty h2

theorem kappa_univ_ne_zero : kappa K Set.univ ≠ 0 := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  rw [kappa, Measure.map_apply (continuous_psi K).measurable MeasurableSet.univ, Set.preimage_univ, rho,
    ← Set.univ_prod_univ, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod]
  refine mul_ne_zero (isOpen_univ.measure_ne_zero _ Set.univ_nonempty)
    (mul_ne_zero (isOpen_univ.measure_ne_zero _ Set.univ_nonempty) (idelicHaarW_univ_ne_zero K))

theorem exists_eq_mul_lintegral_kappa (μB : Measure (adelicBorel (𝓞 K) K)) [μB.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μB] [μB.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ F : adelicBorel (𝓞 K) K → ℝ≥0∞,
      ∫⁻ b, F b ∂μB = c * ∫⁻ b, F b ∂(kappa K) := by
  haveI : μB.IsHaarMeasure := ⟨⟩
  set c' := Measure.haarScalarFactor (kappa K) μB with hc'
  have hκ : kappa K = c' • μB := Measure.isMulLeftInvariant_eq_smul (kappa K) μB
  have hc0 : c' ≠ 0 := by
    intro h0
    apply kappa_univ_ne_zero K
    rw [hκ, h0, zero_smul, Measure.coe_zero, Pi.zero_apply]
  refine ⟨((c' : ℝ≥0∞))⁻¹, ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top, ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hc0),
    fun F => ?_⟩
  have h1 : ∫⁻ b, F b ∂(kappa K) = (c' : ℝ≥0∞) * ∫⁻ b, F b ∂μB := by
    rw [hκ, lintegral_smul_measure]
    rfl
  rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hc0) ENNReal.coe_ne_top, one_mul]

end BorelCoord
p2m_reactivate "P2MW.S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.AutomorphicForm.BorelCoord"

open BorelCoord in
theorem exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant'
    (K : Type) [Field K] [NumberField K]
    (μB : Measure (adelicBorel (𝓞 K) K)) [μB.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μB]
    [μB.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        ∫⁻ b, F (b : AdelicGL2 (𝓞 K) K) ∂μB =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t,
                F (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(adelicAddHaar (𝓞 K) K) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  obtain ⟨c, hc0, hctop, hc⟩ := exists_eq_mul_lintegral_kappa K μB
  refine ⟨c, hc0, hctop, fun F hF => ?_⟩
  rw [hc (fun b => F b)]
  congr 1

  set Φ : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞ := fun p => F (psiG K p) with hΦ_def
  have hΦ : Measurable Φ := hF.comp (continuous_psiG K).measurable
  have hFb : Measurable fun b : adelicBorel (𝓞 K) K => F (b : AdelicGL2 (𝓞 K) K) := hF.comp measurable_subtype_coe
  rw [kappa, lintegral_map hFb (continuous_psi K).measurable]
  change ∫⁻ p, Φ p ∂(rho K) = _
  rw [rho, lintegral_prod _ hΦ.aemeasurable]
  refine lintegral_congr fun x => ?_
  have hΦx : Measurable fun q : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => Φ (x, q) := hΦ.comp measurable_prodMk_left
  rw [lintegral_prod _ hΦx.aemeasurable]
  refine lintegral_congr fun u => ?_
  have hΦxu : Measurable fun t : (AdeleRing (𝓞 K) K)ˣ => Φ (x, u, t) := hΦx.comp measurable_prodMk_left
  rw [idelicHaarW, lintegral_withDensity_eq_lintegral_mul _ (measurable_dens K) hΦxu]
  refine lintegral_congr fun t => ?_
  simp only [Pi.mul_apply, hΦ_def, dens, psiG, mul_comm]

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.AutomorphicForm.BorelCoord P2MW.S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.AutomorphicForm.BorelCoord P2MW.S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.AutomorphicForm"

theorem solution
    (K : Type) [Field K] [NumberField K]
    (μB : MeasureTheory.Measure (AutomorphicForm.adelicBorel (𝓞 K) K)) [μB.IsMulLeftInvariant]
    [MeasureTheory.IsFiniteMeasureOnCompacts μB] [μB.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ F : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        ∫⁻ b, F (b : AutomorphicForm.AdelicGL2 (𝓞 K) K) ∂μB =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t,
                F (AutomorphicForm.unipotentGL2 x * AutomorphicForm.centralScalar (𝓞 K) K u * NumberField.AdelicLevel.diagOne t) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K) :=
  AutomorphicForm.exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant' K μB

end S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant
end P2MW
export P2MW.S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant (solution)
