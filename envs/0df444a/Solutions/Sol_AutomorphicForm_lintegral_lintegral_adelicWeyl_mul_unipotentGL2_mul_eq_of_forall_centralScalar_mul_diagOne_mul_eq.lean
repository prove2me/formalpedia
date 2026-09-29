-- Prove2me | solution 1 for AutomorphicForm.lintegral_lintegral_adelicWeyl_mul_unipotentGL2_mul_eq_of_forall_centralScalar_mul_diagOne_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/be839f5f-50da-561b-a566-3a98b0bcee4c

import Mathlib
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_lintegral_adelicWeyl_mul_unipotentGL2_mul_eq_of_forall_centralScalar_mul_diagOne_mul_eq
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal NNReal Pointwise Topology

noncomputable section

namespace R4W3

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "G" => AdelicGL2 (𝓞 F) F
local notation "I" => (AdeleRing (𝓞 F) F)ˣ
local notation "KK" => adelicMaximalCompact F

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

scoped instance secondCountable_adele : SecondCountableTopology 𝔸 :=
  NumberField.AdeleRing.secondCountableTopology F

scoped instance secondCountable_gl : SecondCountableTopology G :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F

scoped instance secondCountable_mulOpposite_adele : SecondCountableTopology 𝔸ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountable_idele : SecondCountableTopology I :=
  Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompactSpace_idele : LocallyCompactSpace I :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance isAddHaarMeasure_adelicAddHaar' : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure :=
  isAddHaarMeasure_adelicAddHaar (𝓞 F) F

scoped instance isHaarMeasure_adelicGLHaar' : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

scoped instance regular_adelicAddHaar : (adelicAddHaar (𝓞 F) F).Regular := by
  show Measure.Regular (Measure.addHaar)
  unfold Measure.addHaar
  infer_instance

scoped instance regular_idelicHaar : (NumberField.Idele.idelicHaar F).Regular := by
  show Measure.Regular (Measure.haar)
  unfold Measure.haar
  infer_instance

def tau (p : I × I) : G := centralScalar (𝓞 F) F p.1 * diagOne p.2

def P0 (q : KK × 𝔸) : G := unipotentGL2 q.2 * (q.1 : G)

theorem tau_val (p : I × I) :
    ((tau F p : G) : Matrix (Fin 2) (Fin 2) 𝔸) = !![(p.1 : 𝔸) * (p.2 : 𝔸), 0; 0, (p.1 : 𝔸)] := by
  simp only [tau, Units.val_mul]
  have h1 : ((centralScalar (𝓞 F) F p.1 : G) : Matrix (Fin 2) (Fin 2) 𝔸) =
      Matrix.scalar (Fin 2) (p.1 : 𝔸) := rfl
  rw [h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply]

theorem tau_mul (p q : I × I) : tau F (p * q) = tau F p * tau F q := by
  apply Units.ext
  rw [Units.val_mul, tau_val, tau_val, tau_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, Prod.fst_mul, Prod.snd_mul, Units.val_mul]; try ring)

theorem tau_one : tau F 1 = 1 := by
  apply Units.ext
  rw [tau_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem adelicWeyl_val :
    ((adelicWeyl (𝓞 F) F : G) : Matrix (Fin 2) (Fin 2) 𝔸) = !![0, 1; 1, 0] := by
  simp only [adelicWeyl, globalPoints]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem unipotent_mul_tau (x : 𝔸) (p : I × I) :
    unipotentGL2 x * tau F p = tau F p * unipotentGL2 (((p.2⁻¹ : I) : 𝔸) * x) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, tau_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h : ((p.1 : I) : 𝔸) * ((p.2 : I) : 𝔸) * ((((p.2⁻¹ : I)) : 𝔸) * x) = ((p.1 : I) : 𝔸) * x := by
    rw [mul_assoc, ← mul_assoc ((p.2 : I) : 𝔸), Units.mul_inv, one_mul]
  rw [h, mul_comm]

def sigmaT (p : I × I) : I × I := (p.1 * p.2, p.2⁻¹)

theorem adelicWeyl_mul_tau (p : I × I) :
    adelicWeyl (𝓞 F) F * tau F p = tau F (sigmaT F p) * adelicWeyl (𝓞 F) F := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, tau_val, tau_val, adelicWeyl_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, sigmaT]

theorem continuous_hom_of_continuous_val (h : I →* G)
    (hval : Continuous fun t : I => ((h t : G) : Matrix (Fin 2) (Fin 2) 𝔸)) : Continuous h := by
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have : (fun t : I => (((h t)⁻¹ : G) : Matrix (Fin 2) (Fin 2) 𝔸)) =
      (fun t : I => ((h t : G) : Matrix (Fin 2) (Fin 2) 𝔸)) ∘ fun t : I => t⁻¹ := by
    funext t
    simp only [Function.comp_apply, map_inv]
  rw [this]
  exact hval.comp continuous_inv

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 F) F : I → G) := by
  refine continuous_hom_of_continuous_val F _ ?_
  have : (fun u : I => ((centralScalar (𝓞 F) F u : G) : Matrix (Fin 2) (Fin 2) 𝔸)) =
      fun u : I => Matrix.scalar (Fin 2) (u : 𝔸) := rfl
  rw [this]
  exact continuous_matrix fun i j => by
    by_cases hij : i = j
    · subst hij; simpa using Units.continuous_val
    · simp [hij, continuous_const]

theorem continuous_diagOne : Continuous (diagOne : I → G) := by
  refine continuous_hom_of_continuous_val F _ ?_
  refine continuous_matrix fun i j => ?_
  simp only [diagOne_coe_apply]
  fin_cases i <;> fin_cases j
  · simpa using Units.continuous_val
  · simp [continuous_const]
  · simp [continuous_const]
  · simp [continuous_const]

theorem continuous_tau : Continuous (tau F) := by
  unfold tau
  exact ((continuous_centralScalar F).comp continuous_fst).mul ((continuous_diagOne F).comp continuous_snd)

theorem continuous_P0 : Continuous (P0 F) := by
  unfold P0
  exact (AutomorphicForm.continuous_unipotentGL2.comp continuous_snd).mul
    (continuous_subtype_val.comp continuous_fst)

theorem measurable_tau : Measurable (tau F) := (continuous_tau F).measurable

theorem measurable_P0 : Measurable (P0 F) := (continuous_P0 F).measurable

local notation "dx" => adelicAddHaar (𝓞 F) F
local notation "dI" => NumberField.Idele.idelicHaar F
local notation "dT" => Measure.prod (NumberField.Idele.idelicHaar F) (NumberField.Idele.idelicHaar F)
local notation "dk" => AutomorphicForm.maximalCompactHaar F
local notation "dq" => Measure.prod (AutomorphicForm.maximalCompactHaar F) (adelicAddHaar (𝓞 F) F)
local notation "dg" => adelicGLHaar (Fin 2) (𝓞 F) F

def nrm (t : I) : ℝ≥0∞ := ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)

theorem nrm_ne_zero (t : I) : nrm F t ≠ 0 :=
  (ENNReal.ofReal_pos.2 (NumberField.TateGlobal.ideleNorm_pos t)).ne'

theorem nrm_ne_top (t : I) : nrm F t ≠ ⊤ := ENNReal.ofReal_ne_top

theorem nrm_eq_coe (t : I) : nrm F t = ((distribHaarChar 𝔸 t : ℝ≥0) : ℝ≥0∞) := by
  unfold nrm NumberField.TateGlobal.ideleNorm
  exact ENNReal.ofReal_coe_nnreal

theorem nrm_inv (t : I) : nrm F t⁻¹ = (nrm F t)⁻¹ := by
  rw [nrm_eq_coe, nrm_eq_coe, map_inv, ENNReal.coe_inv distribHaarChar_pos.ne']

theorem ofReal_ideleNorm_inv (t : I) :
    ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹) = (nrm F t)⁻¹ :=
  ENNReal.ofReal_inv_of_pos (NumberField.TateGlobal.ideleNorm_pos t)

theorem measurable_nrm : Measurable (nrm F) :=
  ENNReal.measurable_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F).measurable

theorem lintegral_comp_units_mul (v : I) (h : 𝔸 → ℝ≥0∞) :
    ∫⁻ x, h ((v : 𝔸) * x) ∂dx = (nrm F v)⁻¹ * ∫⁻ x, h x ∂dx := by
  have hmap : Measure.map (fun x : 𝔸 => (v : 𝔸) * x) dx = (nrm F v)⁻¹ • dx := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul]
    have hpre : (fun x : 𝔸 => (v : 𝔸) * x) ⁻¹' s = v⁻¹ • s := by
      ext x
      simp only [Set.mem_preimage]
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]
    rw [hpre, ← distribHaarChar_mul dx v⁻¹ s, ← nrm_eq_coe, nrm_inv]
  set e : 𝔸 ≃ᵐ 𝔸 := (Homeomorph.smul v).toMeasurableEquiv with hedef
  have he : (e : 𝔸 → 𝔸) = fun x => (v : 𝔸) * x := by
    funext x; rfl
  calc ∫⁻ x, h ((v : 𝔸) * x) ∂dx = ∫⁻ x, h (e x) ∂dx := by rw [he]
    _ = ∫⁻ y, h y ∂(Measure.map e dx) := (lintegral_map_equiv h e).symm
    _ = ∫⁻ y, h y ∂((nrm F v)⁻¹ • dx) := by rw [he, hmap]
    _ = (nrm F v)⁻¹ * ∫⁻ x, h x ∂dx := by rw [lintegral_smul_measure, smul_eq_mul]

theorem measurePreserving_sigmaT : MeasurePreserving (sigmaT F) dT dT := by
  have h1 : MeasurePreserving (fun z : I × I => (z.1 * z.2, z.2)) dT dT := measurePreserving_mul_prod dI dI
  have h2 : MeasurePreserving (Prod.map id fun t : I => t⁻¹) dT dT :=
    (MeasurePreserving.id dI).prod (Measure.measurePreserving_inv dI)
  have : sigmaT F = (Prod.map id fun t : I => t⁻¹) ∘ fun z : I × I => (z.1 * z.2, z.2) := by
    funext z; rfl
  rw [this]
  exact h2.comp h1

def IwasawaFormula (c : ℝ≥0∞) : Prop :=
  ∀ φ : G → ℝ≥0∞, Measurable φ →
    ∫⁻ g, φ g ∂dg =
      c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
            φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : G)) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
          ∂dk ∂dI ∂dI ∂dx

theorem exists_iwasawaFormula : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ IwasawaFormula F c :=
  NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa F

theorem continuous_param :
    Continuous fun z : (𝔸 × (I × I)) × KK =>
      tau F z.1.2 * (unipotentGL2 ((((z.1.2.2)⁻¹ : I) : 𝔸) * z.1.1) * (z.2 : G)) := by
  refine ((continuous_tau F).comp (continuous_snd.comp continuous_fst)).mul ?_
  refine Continuous.mul ?_ (continuous_subtype_val.comp continuous_snd)
  refine AutomorphicForm.continuous_unipotentGL2.comp ?_
  exact (Units.continuous_val.comp (continuous_inv.comp
    (continuous_snd.comp (continuous_snd.comp continuous_fst)))).mul (continuous_fst.comp continuous_fst)

theorem continuous_param₂ (p : I × I) :
    Continuous fun z : 𝔸 × KK => tau F p * (unipotentGL2 z.1 * (z.2 : G)) :=
  continuous_const.mul ((AutomorphicForm.continuous_unipotentGL2.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd))

def Haux (Φ : G → ℝ≥0∞) (z : 𝔸 × (I × I)) : ℝ≥0∞ :=
  (∫⁻ k, Φ (tau F z.2 * (unipotentGL2 ((((z.2.2)⁻¹ : I) : 𝔸) * z.1) * (k : G))) ∂dk) * (nrm F z.2.2)⁻¹

theorem measurable_Haux (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) : Measurable (Haux F Φ) := by
  refine Measurable.mul ?_ ?_
  · exact (hΦ.comp (continuous_param F).measurable).lintegral_prod_right'
  · exact ((measurable_nrm F).comp (measurable_snd.comp measurable_snd)).inv

theorem step1 (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (x : 𝔸) (u t : I) :
    ∫⁻ k, Φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : G)) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹) ∂dk = Haux F Φ (x, (u, t)) := by
  have hm : Measurable fun k : KK =>
      Φ (tau F (u, t) * (unipotentGL2 ((((t)⁻¹ : I) : 𝔸) * x) * (k : G))) :=
    hΦ.comp (continuous_const.mul (continuous_const.mul continuous_subtype_val)).measurable
  unfold Haux
  rw [ofReal_ideleNorm_inv, ← lintegral_mul_const _ hm]
  refine lintegral_congr fun k => ?_
  rw [mul_assoc (unipotentGL2 x), show centralScalar (𝓞 F) F u * diagOne t = tau F (u, t) from rfl,
    unipotent_mul_tau, mul_assoc]

theorem step3 (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (p : I × I) :
    ∫⁻ x, Haux F Φ (x, p) ∂dx = ∫⁻ q, Φ (tau F p * P0 F q) ∂dq := by
  have hin : Measurable fun z : 𝔸 × KK => Φ (tau F p * (unipotentGL2 z.1 * (z.2 : G))) :=
    hΦ.comp (continuous_param₂ F p).measurable
  have hm2 : Measurable fun x : 𝔸 => ∫⁻ k, Φ (tau F p * (unipotentGL2 x * (k : G))) ∂dk :=
    hin.lintegral_prod_right'
  have hm3 : Measurable fun x : 𝔸 =>
      ∫⁻ k, Φ (tau F p * (unipotentGL2 ((((p.2)⁻¹ : I) : 𝔸) * x) * (k : G))) ∂dk :=
    hm2.comp (measurable_const_mul _)
  have hdil := lintegral_comp_units_mul F (p.2)⁻¹
    (fun x => ∫⁻ k, Φ (tau F p * (unipotentGL2 x * (k : G))) ∂dk)
  beta_reduce at hdil
  unfold Haux
  dsimp only
  rw [lintegral_mul_const _ hm3, hdil, nrm_inv, inv_inv, mul_comm (nrm F p.2), mul_assoc,
    ENNReal.mul_inv_cancel (nrm_ne_zero F _) (nrm_ne_top F _), mul_one,
    lintegral_lintegral_swap hin.aemeasurable]
  have hP : Measurable fun q : KK × 𝔸 => Φ (tau F p * P0 F q) :=
    hΦ.comp (measurable_const.mul (measurable_P0 F))
  symm
  rw [lintegral_prod _ hP.aemeasurable]
  rfl

theorem iform {c : ℝ≥0∞} (hI : IwasawaFormula F c) (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ g, Φ g ∂dg = c * ∫⁻ p, ∫⁻ q, Φ (tau F p * P0 F q) ∂dq ∂dT := by
  rw [hI Φ hΦ]
  congr 1
  have hHm := measurable_Haux F Φ hΦ
  have e1 : (fun x : 𝔸 => ∫⁻ u, ∫⁻ t, ∫⁻ k,
        Φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : G)) *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹) ∂dk ∂dI ∂dI) =
      fun x : 𝔸 => ∫⁻ p, Haux F Φ (x, p) ∂dT := by
    funext x
    have hHx : Measurable fun p : I × I => Haux F Φ (x, p) := hHm.comp measurable_prodMk_left
    rw [lintegral_prod _ hHx.aemeasurable]
    simp_rw [step1 F Φ hΦ]
  rw [e1, lintegral_lintegral_swap (f := fun (x : 𝔸) (p : I × I) => Haux F Φ (x, p)) hHm.aemeasurable]
  exact lintegral_congr fun p => step3 F Φ hΦ p

theorem continuous_act : Continuous fun z : (I × I) × G => tau F z.1 * z.2 :=
  ((continuous_tau F).comp continuous_fst).mul continuous_snd

theorem orbit0 {c : ℝ≥0∞} (hI : IwasawaFormula F c) (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ g, Φ g ∂dg = c * ∫⁻ q, ∫⁻ p, Φ (tau F p * P0 F q) ∂dT ∂dq := by
  have h : Measurable (Function.uncurry fun (p : I × I) (q : KK × 𝔸) => Φ (tau F p * P0 F q)) :=
    hΦ.comp (((continuous_tau F).comp continuous_fst).mul ((continuous_P0 F).comp continuous_snd)).measurable
  rw [iform F hI Φ hΦ, lintegral_lintegral_swap h.aemeasurable]

theorem orbitw {c : ℝ≥0∞} (hI : IwasawaFormula F c) (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ g, Φ g ∂dg = c * ∫⁻ q, ∫⁻ p, Φ (tau F p * (adelicWeyl (𝓞 F) F * P0 F q)) ∂dT ∂dq := by
  have hΦw : Measurable fun g : G => Φ (adelicWeyl (𝓞 F) F * g) := hΦ.comp (measurable_const_mul _)
  rw [← lintegral_mul_left_eq_self Φ (adelicWeyl (𝓞 F) F), orbit0 F hI _ hΦw]
  congr 1
  refine lintegral_congr fun q => ?_
  have e : ∀ p : I × I, adelicWeyl (𝓞 F) F * (tau F p * P0 F q) =
      tau F (sigmaT F p) * (adelicWeyl (𝓞 F) F * P0 F q) := by
    intro p
    rw [← mul_assoc, adelicWeyl_mul_tau, mul_assoc]
  simp_rw [e]
  exact (measurePreserving_sigmaT F).lintegral_comp
    (f := fun p : I × I => Φ (tau F p * (adelicWeyl (𝓞 F) F * P0 F q)))
    (hΦ.comp ((continuous_tau F).mul continuous_const).measurable)

def orb (β : G → ℝ≥0∞) (g : G) : ℝ≥0∞ := ∫⁻ p, β (tau F p * g) ∂dT

theorem measurable_orb (β : G → ℝ≥0∞) (hβ : Measurable β) : Measurable (orb F β) :=
  (hβ.comp (continuous_act F).measurable).lintegral_prod_left'

theorem orb_tau_mul (β : G → ℝ≥0∞) (p₀ : I × I) (g : G) : orb F β (tau F p₀ * g) = orb F β g := by
  unfold orb
  have e : ∀ p : I × I, β (tau F p * (tau F p₀ * g)) = β (tau F (p * p₀) * g) := by
    intro p; rw [tau_mul, mul_assoc]
  simp_rw [e]
  exact lintegral_mul_right_eq_self (fun p : I × I => β (tau F p * g)) p₀

theorem key {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hI : IwasawaFormula F c)
    (f β : G → ℝ≥0∞) (hf : Measurable f) (hβ : Measurable β)
    (hinv : ∀ (u t : I) (g : G), f (centralScalar (𝓞 F) F u * diagOne t * g) = f g) :
    ∫⁻ q, f (P0 F q) * orb F β (P0 F q) ∂dq =
      ∫⁻ q, f (adelicWeyl (𝓞 F) F * P0 F q) * orb F β (adelicWeyl (𝓞 F) F * P0 F q) ∂dq := by
  have hinv' : ∀ (p : I × I) (g : G), f (tau F p * g) = f g := fun p g => hinv p.1 p.2 g
  have hm : Measurable fun g => β g * f g := hβ.mul hf
  have horb : ∀ g : G, ∫⁻ p, β (tau F p * g) * f (tau F p * g) ∂dT = f g * orb F β g := by
    intro g
    have hm' : Measurable fun p : I × I => β (tau F p * g) :=
      hβ.comp ((continuous_tau F).mul continuous_const).measurable
    simp_rw [hinv']
    rw [lintegral_mul_const _ hm', mul_comm]
    rfl
  have h0 := orbit0 F hI (fun g => β g * f g) hm
  have hw := orbitw F hI (fun g => β g * f g) hm
  simp only [horb] at h0 hw
  rw [h0] at hw
  exact (ENNReal.mul_right_inj hc0 hct).1 hw

def V (C : Set G) : G → ℝ≥0∞ := orb F (C.indicator 1)

def βn (C : Set G) : G → ℝ≥0∞ := C.indicator fun g => (V F C g)⁻¹

def U (C : Set G) : Set G := V F C ⁻¹' ({0}ᶜ ∩ {⊤}ᶜ)

theorem mem_U {C : Set G} {g : G} : g ∈ U F C ↔ V F C g ≠ 0 ∧ V F C g ≠ ⊤ := by
  simp [U]

theorem measurable_V {C : Set G} (hC : MeasurableSet C) : Measurable (V F C) :=
  measurable_orb F _ (measurable_one.indicator hC)

theorem measurableSet_U {C : Set G} (hC : MeasurableSet C) : MeasurableSet (U F C) :=
  measurable_V F hC ((measurableSet_singleton 0).compl.inter (measurableSet_singleton ⊤).compl)

theorem measurable_βn {C : Set G} (hC : MeasurableSet C) : Measurable (βn F C) :=
  (measurable_V F hC).inv.indicator hC

theorem V_tau_mul (C : Set G) (p : I × I) (g : G) : V F C (tau F p * g) = V F C g :=
  orb_tau_mul F _ p g

theorem orb_βn {C : Set G} (hC : MeasurableSet C) (g : G) :
    orb F (βn F C) g = (U F C).indicator 1 g := by
  have e : ∀ p : I × I, βn F C (tau F p * g) = (V F C g)⁻¹ * C.indicator 1 (tau F p * g) := by
    intro p
    unfold βn
    by_cases h : tau F p * g ∈ C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, V_tau_mul, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  have hm' : Measurable fun p : I × I => C.indicator (1 : G → ℝ≥0∞) (tau F p * g) :=
    (measurable_one.indicator hC).comp ((continuous_tau F).mul continuous_const).measurable
  unfold orb
  simp_rw [e]
  rw [lintegral_const_mul _ hm']
  change (V F C g)⁻¹ * V F C g = _
  by_cases h0 : V F C g = 0
  · rw [h0, mul_zero, Set.indicator_of_notMem ((mem_U F).not.2 (by simp [h0]))]
  by_cases ht : V F C g = ⊤
  · rw [ht, ENNReal.inv_top, zero_mul, Set.indicator_of_notMem ((mem_U F).not.2 (by simp [ht]))]
  · rw [ENNReal.inv_mul_cancel h0 ht, Set.indicator_of_mem ((mem_U F).2 ⟨h0, ht⟩), Pi.one_apply]

def tauHom : (I × I) →* G where
  toFun := tau F
  map_one' := tau_one F
  map_mul' := tau_mul F

theorem tau_inv (p : I × I) : tau F p⁻¹ = (tau F p)⁻¹ := map_inv (tauHom F) p

def readOut (g : G) : (𝔸 × 𝔸ᵐᵒᵖ) × (𝔸 × 𝔸ᵐᵒᵖ) :=
  (((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1, MulOpposite.op (((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1)),
    ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0 * ((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1,
      MulOpposite.op (((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1) * ((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) 𝔸) 0 0)))

theorem continuous_readOut : Continuous (readOut F) := by
  have hv : ∀ i j : Fin 2, Continuous fun g : G => (g : Matrix (Fin 2) (Fin 2) 𝔸) i j :=
    fun i j => (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) 𝔸)).matrix_elem i j
  have hi : ∀ i j : Fin 2, Continuous fun g : G => ((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) 𝔸) i j :=
    fun i j => (Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) 𝔸)).matrix_elem i j
  unfold readOut
  exact ((hv 1 1).prodMk (MulOpposite.continuous_op.comp (hi 1 1))).prodMk
    (((hv 0 0).mul (hi 1 1)).prodMk (MulOpposite.continuous_op.comp ((hv 1 1).mul (hi 0 0))))

theorem readOut_tau (p : I × I) :
    readOut F (tau F p) = Prod.map (Units.embedProduct 𝔸) (Units.embedProduct 𝔸) p := by
  rw [readOut, ← tau_inv, tau_val, tau_val]
  simp only [Prod.map, Units.embedProduct_apply, Prod.fst_inv, Prod.snd_inv]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  refine Prod.ext (Prod.ext rfl rfl) (Prod.ext ?_ ?_)
  · show (p.1 : 𝔸) * (p.2 : 𝔸) * ((p.1⁻¹ : I) : 𝔸) = (p.2 : 𝔸)
    rw [mul_comm (p.1 : 𝔸), mul_assoc, Units.mul_inv, mul_one]
  · show MulOpposite.op ((p.1 : 𝔸) * (((p.1⁻¹ : I) : 𝔸) * ((p.2⁻¹ : I) : 𝔸))) =
      MulOpposite.op ((p.2⁻¹ : I) : 𝔸)
    rw [← mul_assoc, Units.mul_inv, one_mul]

theorem isCompact_preimage_tau {C : Set G} (hC : IsCompact C) : IsCompact (tau F ⁻¹' C) := by
  have hE : Topology.IsClosedEmbedding (Prod.map (Units.embedProduct 𝔸) (Units.embedProduct 𝔸)) :=
    Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct
  have hsub : tau F ⁻¹' C ⊆ Prod.map (Units.embedProduct 𝔸) (Units.embedProduct 𝔸) ⁻¹' (readOut F '' C) := by
    intro p hp
    exact ⟨tau F p, hp, readOut_tau F p⟩
  exact (hE.isCompact_preimage (hC.image (continuous_readOut F))).of_isClosed_subset
    (hC.isClosed.preimage (continuous_tau F)) hsub

theorem V_eq_measure {C : Set G} (hC : MeasurableSet C) (g : G) :
    V F C g = dT ((fun p : I × I => tau F p * g) ⁻¹' C) := by
  have hS : MeasurableSet ((fun p : I × I => tau F p * g) ⁻¹' C) :=
    hC.preimage ((continuous_tau F).mul continuous_const).measurable
  unfold V orb
  rw [← lintegral_indicator_one hS]
  rfl

theorem V_lt_top {C : Set G} (hC : IsCompact C) (g : G) : V F C g < ⊤ := by
  rw [V_eq_measure F hC.measurableSet]
  have : (fun p : I × I => tau F p * g) ⁻¹' C = tau F ⁻¹' ((Homeomorph.mulRight g) ⁻¹' C) := rfl
  rw [this]
  exact (isCompact_preimage_tau F ((Homeomorph.mulRight g).isCompact_preimage.2 hC)).measure_lt_top

theorem V_ne_zero {C : Set G} (hC : MeasurableSet C) {g : G} (hg : g ∈ interior C) : V F C g ≠ 0 := by
  rw [V_eq_measure F hC]
  have hopen : IsOpen ((fun p : I × I => tau F p * g) ⁻¹' interior C) :=
    isOpen_interior.preimage ((continuous_tau F).mul continuous_const)
  have hne : ((fun p : I × I => tau F p * g) ⁻¹' interior C).Nonempty :=
    ⟨1, by simpa [tau_one] using hg⟩
  exact (lt_of_lt_of_le (hopen.measure_pos dT hne) (measure_mono (Set.preimage_mono interior_subset))).ne'

theorem V_mono {C C' : Set G} (h : C ⊆ C') (g : G) : V F C g ≤ V F C' g := by
  unfold V orb
  exact lintegral_mono fun p => Set.indicator_le_indicator_of_subset h (fun _ => bot_le) _

theorem main (f : G → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ (u t : I) (g : G), f (centralScalar (𝓞 F) F u * diagOne t * g) = f g) :
    ∫⁻ k, ∫⁻ x, f (adelicWeyl (𝓞 F) F * unipotentGL2 x * (k : G)) ∂dx ∂dk =
      ∫⁻ k, ∫⁻ x, f (unipotentGL2 x * (k : G)) ∂dx ∂dk := by
  obtain ⟨c, hc0, hct, hI⟩ := exists_iwasawaFormula F
  set Kx : CompactExhaustion G := CompactExhaustion.choice G with hKx

  have hmeasK : ∀ j, MeasurableSet (Kx j) := fun j => (Kx.isCompact j).measurableSet
  have hUmono : ∀ {i j : ℕ}, i ≤ j → U F (Kx i) ⊆ U F (Kx j) := by
    intro i j hij g hg
    rw [mem_U] at hg ⊢
    exact ⟨fun h0 => hg.1 (le_antisymm (le_trans (V_mono F (Kx.subset hij) g) h0.le) bot_le),
      (V_lt_top F (Kx.isCompact j) g).ne⟩
  have hcover : ∀ g : G, ∃ j, g ∈ U F (Kx j) := by
    intro g
    obtain ⟨j, hj⟩ := Kx.exists_mem g
    refine ⟨j + 1, (mem_U F).2 ⟨?_, (V_lt_top F (Kx.isCompact (j + 1)) g).ne⟩⟩
    exact V_ne_zero F (hmeasK (j + 1)) (Kx.subset_interior_succ j hj)
  have hsup : ∀ g : G, (⨆ j, (U F (Kx j)).indicator (1 : G → ℝ≥0∞) g) = 1 := by
    intro g
    refine le_antisymm (iSup_le fun j => Set.indicator_apply_le' (fun _ => le_rfl) fun _ => bot_le) ?_
    obtain ⟨j, hj⟩ := hcover g
    exact le_iSup_of_le j (by rw [Set.indicator_of_mem hj, Pi.one_apply])

  have hP := measurable_P0 F
  have hwP : Measurable fun q : KK × 𝔸 => adelicWeyl (𝓞 F) F * P0 F q := measurable_const.mul hP
  have hm1 : Measurable fun q : KK × 𝔸 => f (P0 F q) := hf.comp hP
  have hm2 : Measurable fun q : KK × 𝔸 => f (adelicWeyl (𝓞 F) F * P0 F q) := hf.comp hwP
  have hL : ∫⁻ k, ∫⁻ x, f (unipotentGL2 x * (k : G)) ∂dx ∂dk = ∫⁻ q, f (P0 F q) ∂dq := by
    rw [lintegral_prod _ hm1.aemeasurable]
    rfl
  have hR : ∫⁻ k, ∫⁻ x, f (adelicWeyl (𝓞 F) F * unipotentGL2 x * (k : G)) ∂dx ∂dk =
      ∫⁻ q, f (adelicWeyl (𝓞 F) F * P0 F q) ∂dq := by
    rw [lintegral_prod _ hm2.aemeasurable]
    simp_rw [mul_assoc]
    rfl
  rw [hL, hR]

  have hkey : ∀ j, ∫⁻ q, f (P0 F q) * (U F (Kx j)).indicator 1 (P0 F q) ∂dq =
      ∫⁻ q, f (adelicWeyl (𝓞 F) F * P0 F q) *
        (U F (Kx j)).indicator 1 (adelicWeyl (𝓞 F) F * P0 F q) ∂dq := by
    intro j
    simp_rw [← orb_βn F (hmeasK j)]
    exact key F hc0 hct hI f (βn F (Kx j)) hf (measurable_βn F (hmeasK j)) hinv

  have hind : ∀ j, Measurable ((U F (Kx j)).indicator (1 : G → ℝ≥0∞)) :=
    fun j => measurable_one.indicator (measurableSet_U F (hmeasK j))
  have hmono : ∀ (P : KK × 𝔸 → G), Monotone fun j => fun q : KK × 𝔸 =>
      f (P q) * (U F (Kx j)).indicator (1 : G → ℝ≥0∞) (P q) := by
    intro P i j hij q
    exact mul_le_mul_right (Set.indicator_le_indicator_of_subset (hUmono hij) (fun _ => bot_le) _) _
  have hlim : ∀ (P : KK × 𝔸 → G), Measurable P →
      ∫⁻ q, f (P q) ∂dq = ⨆ j, ∫⁻ q, f (P q) * (U F (Kx j)).indicator (1 : G → ℝ≥0∞) (P q) ∂dq := by
    intro P hPm
    have hmj : ∀ j, Measurable fun q : KK × 𝔸 =>
        f (P q) * (U F (Kx j)).indicator (1 : G → ℝ≥0∞) (P q) :=
      fun j => (hf.comp hPm).mul ((hind j).comp hPm)
    rw [← lintegral_iSup hmj (hmono P)]
    refine lintegral_congr fun q => ?_
    rw [← ENNReal.mul_iSup, hsup, mul_one]
  rw [hlim _ hP, hlim _ hwP]
  simp_rw [hkey]

end R4W3
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_lintegral_adelicWeyl_mul_unipotentGL2_mul_eq_of_forall_centralScalar_mul_diagOne_mul_eq.R4W3"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    (f : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (_hf : Measurable f)
    (_hinv : ∀ (u t : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      f (centralScalar (𝓞 F) F u * diagOne t * g) = f g) :
    ∫⁻ k, ∫⁻ x, f (adelicWeyl (𝓞 F) F * unipotentGL2 x * (k : AdelicGL2 (𝓞 F) F))
        ∂(adelicAddHaar (𝓞 F) F) ∂(AutomorphicForm.maximalCompactHaar F) =
      ∫⁻ k, ∫⁻ x, f (unipotentGL2 x * (k : AdelicGL2 (𝓞 F) F))
        ∂(adelicAddHaar (𝓞 F) F) ∂(AutomorphicForm.maximalCompactHaar F) :=
  R4W3.main F f _hf _hinv

end
end S_AutomorphicForm_lintegral_lintegral_adelicWeyl_mul_unipotentGL2_mul_eq_of_forall_centralScalar_mul_diagOne_mul_eq
end P2MW
export P2MW.S_AutomorphicForm_lintegral_lintegral_adelicWeyl_mul_unipotentGL2_mul_eq_of_forall_centralScalar_mul_diagOne_mul_eq (solution)
