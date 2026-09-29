-- Prove2me | solution 1 for AutomorphicForm.measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ba31ec1f-a0a6-5b5f-973e-f4af535087b9

import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one
import Theorems.Thm_AutomorphicForm_exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one
import Theorems.Thm_NumberField_AdeleRing_dedekindZeta_two_mul_pi_measure_setOf_forall_not_norm_lt_one_eq_pi_measure_setOf_forall_mem_adicCompletionIntegers
import Theorems.Thm_AutomorphicForm_setLIntegral_ofReal_norm_det_eq_mul_two_pow_mul_two_pi_pow_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing
import Theorems.Thm_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing
import Theorems.Thm_NumberField_AdelicBox_measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.cpowChar_apply_val ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.InfinitePlace IsDedekindDomain
open scoped ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one setLIntegral_ofReal_norm_det_eq_mul_two_pow_mul_two_pi_pow_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing glBorelOf borelSpace_glBorelOf localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet localGLBorel borelSpace_localGLBorel unitFinSet isOpen_unitFinSet unitFinSet_eq_finiteIntegralGL2 exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing"
namespace WeilConstant
p2m_open "AutomorphicForm"

open scoped Classical

attribute [local instance 2000] NumberField.AdelicHaar.glBorel

section Setup

variable (K : Type) [Field K] [NumberField K]

abbrev Kinf : Type := InfiniteAdeleRing K

abbrev Mix : Type := mixedEmbedding.mixedSpace K

abbrev Ad : Type := AdeleRing (𝓞 K) K

abbrev Adf : Type := FiniteAdeleRing (𝓞 K) K

abbrev Gp : Type := GL (Fin 2) (AdeleRing (𝓞 K) K)

abbrev Ga : Type := GL (Fin 2) (InfiniteAdeleRing K)

abbrev eK : Kinf K ≃+* Mix K := InfiniteAdeleRing.ringEquiv_mixedSpace K

theorem continuous_eK : Continuous (eK K) := NumberField.AdelicBox.continuous_ringEquiv_mixedSpace K

scoped instance mMK : MeasurableSpace (Matrix (Fin 2) (Fin 2) (Kinf K)) := borel _
scoped instance bMK : BorelSpace (Matrix (Fin 2) (Fin 2) (Kinf K)) := ⟨rfl⟩
scoped instance mGa : MeasurableSpace (Ga K) := AutomorphicForm.glBorelOf (Kinf K)
scoped instance bGa : BorelSpace (Ga K) := AutomorphicForm.borelSpace_glBorelOf _
scoped instance bPiMix : BorelSpace (Fin 2 → Mix K) := Pi.borelSpace
scoped instance mGv (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) :=
  AutomorphicForm.localGLBorel K v
scoped instance bGv (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (GL (Fin 2) (v.adicCompletion K)) :=
  AutomorphicForm.borelSpace_localGLBorel K v

scoped instance t2MK : T2Space (Matrix (Fin 2) (Fin 2) (Kinf K)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → Kinf K))
scoped instance lcMK : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (Kinf K)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → Kinf K))
scoped instance lcGa : LocallyCompactSpace (Ga K) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem measurable_valA : Measurable fun g : Ga K => (g : Matrix (Fin 2) (Fin 2) (Kinf K)) :=
  Units.continuous_val.measurable

scoped instance borelSpace_G : BorelSpace (Gp K) := borelSpace_glBorel _ _ _

scoped instance secondCountable_A : SecondCountableTopology (Ad K) :=
  NumberField.AdeleRing.secondCountableTopology K

scoped instance secondCountable_G : SecondCountableTopology (Gp K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

scoped instance secondCountable_units : SecondCountableTopology (Ad K)ˣ := by
  haveI : SecondCountableTopology (Ad K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

end Setup

section Sets

variable (K : Type) [Field K] [NumberField K]

def cube : Set (Mix K) :=
  {z | (∀ w : {w : InfinitePlace K // w.IsReal}, z.1 w ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ w : {w : InfinitePlace K // w.IsComplex},
      (z.2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧ (z.2 w).im ∈ Set.Icc (0 : ℝ) 1}

def sqC : Set ℂ := {z | z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (0 : ℝ) 1}

theorem measurableSet_sqC : MeasurableSet sqC := by
  have : sqC = Complex.measurableEquivRealProd ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    ext z
    simp only [sqC, Set.mem_setOf_eq, Set.mem_preimage, Complex.measurableEquivRealProd_apply, Set.mem_prod]
  rw [this]
  exact (measurableSet_Icc.prod measurableSet_Icc).preimage Complex.measurableEquivRealProd.measurable

theorem cube_eq_prod :
    cube K = (Set.univ.pi fun _ : {w : InfinitePlace K // w.IsReal} => Set.Icc (0 : ℝ) 1) ×ˢ
      (Set.univ.pi fun _ : {w : InfinitePlace K // w.IsComplex} => sqC) := by
  ext z
  simp only [cube, sqC, Set.mem_setOf_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]

theorem measurableSet_cube : MeasurableSet (cube K) := by
  rw [cube_eq_prod]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Icc).prod (MeasurableSet.univ_pi fun _ => measurableSet_sqC)

def Ebox : Set (Ad K) :=
  {x | ((∀ w : {w : InfinitePlace K // w.IsReal},
          (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ w : {w : InfinitePlace K // w.IsComplex},
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
      x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K}

theorem mem_Ebox_iff (x : Ad K) :
    x ∈ Ebox K ↔ InfiniteAdeleRing.ringEquiv_mixedSpace K x.1 ∈ cube K ∧
      ∀ v : HeightOneSpectrum (𝓞 K), x.2 v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]

scoped instance borelSpace_pi : BorelSpace (Fin 2 → Ad K) := Pi.borelSpace

private theorem _root_.AutomorphicForm.WeilConstant.isClosed_integralFiniteAdeles :
    IsClosed (NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K) :=
  NumberField.AdelicBox.isClosed_integralFiniteAdeles K

p2m_export "AutomorphicForm.WeilConstant" "isClosed_integralFiniteAdeles"
theorem measurableSet_Ebox : MeasurableSet (Ebox K) := by
  have h : Ebox K = ((fun x : Ad K => eK K x.1) ⁻¹' cube K) ∩
      ((fun x : Ad K => x.2) ⁻¹' NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K) := by
    ext x; exact mem_Ebox_iff K x
  rw [h]
  have hc1 : Continuous fun x : Ad K => eK K x.1 := (continuous_eK K).comp continuous_fst
  have hc2 : Continuous fun x : Ad K => x.2 := continuous_snd
  exact (hc1.measurable (measurableSet_cube K)).inter
    ((isClosed_integralFiniteAdeles K).preimage hc2).measurableSet

theorem Ebox_ne_zero_ne_top (μ : Measure (Ad K)) (hμ : μ.IsAddHaarMeasure) :
    μ (Ebox K) ≠ 0 ∧ μ (Ebox K) ≠ ⊤ := by
  have h := NumberField.AdelicBox.measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr K μ hμ
  exact ⟨h.1, h.2.1⟩

def Sh : Set (Ad K)ˣ :=
  {u | (∀ v : HeightOneSpectrum (𝓞 K),
      ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
      (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
        v.adicCompletionIntegers K) ∧
    ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)}

theorem continuous_finEval (v : HeightOneSpectrum (𝓞 K)) : Continuous fun x : Adf K => x v :=
  (RestrictedProduct.continuous_eval v :
    Continuous fun x : RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite => x v)

theorem isClosed_integers (v : HeightOneSpectrum (𝓞 K)) :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isClosed_valuationSubring _

theorem isClosed_Sh : IsClosed (Sh K) := by
  have h : Sh K =
      (⋂ v : HeightOneSpectrum (𝓞 K),
        ((fun u : (Ad K)ˣ => ((u : Ad K).2 : Adf K) v) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ∩
         (fun u : (Ad K)ˣ => (((u⁻¹ : (Ad K)ˣ) : Ad K).2 : Adf K) v) ⁻¹'
           (v.adicCompletionIntegers K : Set (v.adicCompletion K)))) ∩
      ⋂ w : InfinitePlace K, (fun u : (Ad K)ˣ => ‖(u : Ad K).1 w‖) ⁻¹' Set.Icc (1 : ℝ) (Real.exp 1) := by
    ext u
    simp only [Sh, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [h]
  refine (isClosed_iInter fun v => (IsClosed.inter ?_ ?_)).inter (isClosed_iInter fun w => ?_)
  · exact (isClosed_integers K v).preimage
      ((continuous_finEval K v).comp (continuous_snd.comp Units.continuous_val))
  · exact (isClosed_integers K v).preimage
      ((continuous_finEval K v).comp (continuous_snd.comp Units.continuous_coe_inv))
  · exact isClosed_Icc.preimage
      (continuous_norm.comp ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val)))

theorem measurableSet_Sh [MeasurableSpace (Ad K)ˣ] [BorelSpace (Ad K)ˣ] : MeasurableSet (Sh K) :=
  (isClosed_Sh K).measurableSet

theorem norm_inv_fst_le_of_mem_Sh {u : (Ad K)ˣ} (hu : u ∈ Sh K) (w : InfinitePlace K) :
    ‖(((u⁻¹ : (Ad K)ˣ) : Ad K).1) w‖ ≤ 1 := by
  have hmul : (((u⁻¹ : (Ad K)ˣ) : Ad K).1) w * ((u : Ad K).1) w = 1 := by
    have h := congrArg (fun x : Ad K => x.1 w) u.inv_mul
    exact h
  have h1 : 1 ≤ ‖((u : Ad K).1) w‖ := (hu.2 w).1
  have hn := congrArg norm hmul
  rw [norm_mul, norm_one] at hn
  have h0 : 0 ≤ ‖(((u⁻¹ : (Ad K)ˣ) : Ad K).1) w‖ := norm_nonneg _
  nlinarith

theorem measure_Sh_lt_top [MeasurableSpace (Ad K)ˣ] (ν : Measure (Ad K)ˣ) [IsFiniteMeasureOnCompacts ν] :
    ν (Sh K) < ⊤ := by
  haveI : ∀ w : InfinitePlace K, ProperSpace w.Completion := fun w => NumberField.AdelicBox.properSpace_completion K w

  set A : Set (Ad K) := {x | (∀ w : InfinitePlace K, ‖x.1 w‖ ≤ Real.exp 1) ∧
    x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K} with hA
  have hAc : IsCompact A := by
    have hA' : A = (Set.univ.pi fun w : InfinitePlace K => Metric.closedBall (0 : w.Completion) (Real.exp 1)) ×ˢ
        NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K := by
      ext x
      exact ⟨fun h => ⟨fun w _ => mem_closedBall_zero_iff.2 (h.1 w), h.2⟩,
        fun h => ⟨fun w => mem_closedBall_zero_iff.1 (h.1 w (Set.mem_univ _)), h.2⟩⟩
    rw [hA']
    exact (isCompact_univ_pi fun w => isCompact_closedBall _ _).prod
      (NumberField.AdelicBox.isCompact_integralFiniteAdeles K)
  have hpre : IsCompact ((Units.embedProduct (Ad K)) ⁻¹' (A ×ˢ (MulOpposite.op '' A))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hAc.prod (hAc.image MulOpposite.continuous_op))
  have hsub : Sh K ⊆ (Units.embedProduct (Ad K)) ⁻¹' (A ×ˢ (MulOpposite.op '' A)) := by
    intro u hu
    simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
    refine ⟨⟨fun w => (hu.2 w).2, fun v => (hu.1 v).1⟩, ⟨((u⁻¹ : (Ad K)ˣ) : Ad K), ⟨fun w => ?_, fun v => (hu.1 v).2⟩, rfl⟩⟩
    exact (norm_inv_fst_le_of_mem_Sh K hu w).trans (Real.one_lt_exp_iff.2 one_pos).le
  exact (measure_mono hsub).trans_lt hpre.measure_lt_top

def P1 : Set (Fin 2 → Ad K) :=
  {c : Fin 2 → AdeleRing (𝓞 K) K |
    (InfiniteAdeleRing.ringEquiv_mixedSpace K (c 0).1, InfiniteAdeleRing.ringEquiv_mixedSpace K (c 1).1) ∈
        cube K ×ˢ cube K ∧
    (∀ v : HeightOneSpectrum (𝓞 K),
      (c 0).2 v ∈ v.adicCompletionIntegers K ∧ (c 1).2 v ∈ v.adicCompletionIntegers K) ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ¬ (‖(c 0).2 v‖ < 1 ∧ ‖(c 1).2 v‖ < 1)}

def B1 : Set (Fin 2 → Ad K) :=
  {c : Fin 2 → AdeleRing (𝓞 K) K |
    (InfiniteAdeleRing.ringEquiv_mixedSpace K (c 0).1, InfiniteAdeleRing.ringEquiv_mixedSpace K (c 1).1) ∈
        cube K ×ˢ cube K ∧
    ∀ v : HeightOneSpectrum (𝓞 K),
      (c 0).2 v ∈ v.adicCompletionIntegers K ∧ (c 1).2 v ∈ v.adicCompletionIntegers K}

theorem P1_subset_B1 : P1 K ⊆ B1 K := fun _ hc => ⟨hc.1, hc.2.1⟩

theorem B1_eq_pi : B1 K = Set.univ.pi fun _ : Fin 2 => Ebox K := by
  ext c
  simp only [B1, Set.mem_setOf_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, mem_Ebox_iff,
    Fin.forall_fin_two, forall_and]

theorem continuous_col_fin (i : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous fun c : Fin 2 → Ad K => ((c i).2 : Adf K) v :=
  (continuous_finEval K v).comp (continuous_snd.comp (continuous_apply i))

theorem continuous_col_arch (i : Fin 2) : Continuous fun c : Fin 2 → Ad K => eK K (c i).1 :=
  (continuous_eK K).comp (continuous_fst.comp (continuous_apply i))

theorem measurableSet_P1 : MeasurableSet (P1 K) := by
  have h : P1 K =
      ((fun c : Fin 2 → Ad K => (eK K (c 0).1, eK K (c 1).1)) ⁻¹' (cube K ×ˢ cube K)) ∩
      ((⋂ v : HeightOneSpectrum (𝓞 K),
        ((fun c : Fin 2 → Ad K => ((c 0).2 : Adf K) v) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ∩
         (fun c : Fin 2 → Ad K => ((c 1).2 : Adf K) v) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)))) ∩
       ⋂ v : HeightOneSpectrum (𝓞 K),
        {c : Fin 2 → Ad K | ‖((c 0).2 : Adf K) v‖ < 1 ∧ ‖((c 1).2 : Adf K) v‖ < 1}ᶜ) := by
    ext c
    simp only [P1, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe,
      Set.mem_compl_iff]
  rw [h]
  refine MeasurableSet.inter ?_ (IsClosed.measurableSet (IsClosed.inter ?_ ?_))
  · exact ((continuous_col_arch K 0).prodMk (continuous_col_arch K 1)).measurable
      ((measurableSet_cube K).prod (measurableSet_cube K))
  · exact isClosed_iInter fun v =>
      ((isClosed_integers K v).preimage (continuous_col_fin K 0 v)).inter
        ((isClosed_integers K v).preimage (continuous_col_fin K 1 v))
  · refine isClosed_iInter fun v => IsOpen.isClosed_compl ?_
    exact (isOpen_lt (continuous_norm.comp (continuous_col_fin K 0 v)) continuous_const).inter
      (isOpen_lt (continuous_norm.comp (continuous_col_fin K 1 v)) continuous_const)

theorem measure_B1 (μ : Measure (Ad K)) [SigmaFinite μ] :
    (Measure.pi fun _ : Fin 2 => μ) (B1 K) = μ (Ebox K) ^ 2 := by
  rw [B1_eq_pi, Measure.pi_pi]
  simp only [Fin.prod_const]

theorem zeta_mul_measure_P1 (μ : Measure (Ad K)) (hμ : μ.IsAddHaarMeasure) :
    ENNReal.ofReal (NumberField.dedekindZeta K 2).re * (Measure.pi fun _ : Fin 2 => μ) (P1 K) =
      μ (Ebox K) ^ 2 := by
  haveI := hμ
  rw [← measure_B1]
  exact NumberField.AdeleRing.dedekindZeta_two_mul_pi_measure_setOf_forall_not_norm_lt_one_eq_pi_measure_setOf_forall_mem_adicCompletionIntegers
    K μ hμ (cube K ×ˢ cube K) ((measurableSet_cube K).prod (measurableSet_cube K))

def Ψt (p : (Fin 2 → Ad K) × (Ad K)ˣ) : ℝ≥0∞ :=
  (P1 K ×ˢ Sh K).indicator (fun p => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K p.2)) p

variable [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

theorem measurable_Ψt : Measurable (Ψt K) := by
  unfold Ψt
  refine Measurable.indicator ?_ ((measurableSet_P1 K).prod (measurableSet_Sh K))
  exact ENNReal.measurable_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm K).measurable.comp measurable_snd)

theorem I_Ψt (μ : Measure (Ad K)) [SigmaFinite μ] (ν : Measure (Ad K)ˣ) :
    ∫⁻ p, ∫⁻ δ, Ψt K (p, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
        ∂(Measure.pi fun _ : Fin 2 => μ) =
      (Measure.pi fun _ : Fin 2 => μ) (P1 K) * ν (Sh K) := by
  have hpt : ∀ (p : Fin 2 → Ad K) (δ : (Ad K)ˣ),
      Ψt K (p, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ =
        (P1 K).indicator (fun _ => (1 : ℝ≥0∞)) p * (Sh K).indicator (fun _ => (1 : ℝ≥0∞)) δ := by
    intro p δ
    by_cases hp : p ∈ P1 K
    · by_cases hδ : δ ∈ Sh K
      · have hmem : (p, δ) ∈ P1 K ×ˢ Sh K := ⟨hp, hδ⟩
        rw [Ψt, Set.indicator_of_mem hmem, Set.indicator_of_mem hp, Set.indicator_of_mem hδ, one_mul,
          ← ENNReal.ofReal_mul (NumberField.TateGlobal.ideleNorm_pos δ).le,
          mul_inv_cancel₀ (NumberField.TateGlobal.ideleNorm_pos δ).ne', ENNReal.ofReal_one]
      · have hmem : (p, δ) ∉ P1 K ×ˢ Sh K := fun h => hδ h.2
        rw [Ψt, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hδ, zero_mul, mul_zero]
    · have hmem : (p, δ) ∉ P1 K ×ˢ Sh K := fun h => hp h.1
      rw [Ψt, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hp, zero_mul, zero_mul]
  simp_rw [hpt]
  have hin : ∀ p : Fin 2 → Ad K,
      ∫⁻ δ, (P1 K).indicator (fun _ => (1 : ℝ≥0∞)) p * (Sh K).indicator (fun _ => (1 : ℝ≥0∞)) δ ∂ν =
        (P1 K).indicator (fun _ => ν (Sh K)) p := by
    intro p
    rw [lintegral_const_mul' _ _ (by
      by_cases hp : p ∈ P1 K
      · rw [Set.indicator_of_mem hp]; exact ENNReal.one_ne_top
      · rw [Set.indicator_of_notMem hp]; exact ENNReal.zero_ne_top),
      lintegral_indicator_const (measurableSet_Sh K), one_mul]
    by_cases hp : p ∈ P1 K
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, one_mul]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, zero_mul]
  simp_rw [hin]
  rw [lintegral_indicator_const (measurableSet_P1 K), mul_comm]

end Sets

section Finite

variable (K : Type) [Field K] [NumberField K]

theorem s_ne_top (τa : Measure (Ga K)) (hτa : τa.IsHaarMeasure) (s : ℝ≥0∞)
    (ρ : Measure (Matrix (Fin 2) (Fin 2) (Kinf K)))
    (hmap : Measure.map (fun t : Ga K => (t : Matrix (Fin 2) (Fin 2) (Kinf K))) τa = s • ρ) : s ≠ ⊤ := by
  haveI := hτa
  intro hs
  obtain ⟨C⟩ := (TopologicalSpace.PositiveCompacts.nonempty' : Nonempty (TopologicalSpace.PositiveCompacts (Ga K)))
  have hpos : 0 < τa C := Measure.measure_pos_of_nonempty_interior τa C.interior_nonempty
  have hlt : τa C < ⊤ := C.isCompact.measure_lt_top

  set D : Set (Matrix (Fin 2) (Fin 2) (Kinf K)) := (fun t : Ga K => (t : Matrix (Fin 2) (Fin 2) (Kinf K))) '' (C : Set (Ga K))
  have hDc : IsCompact D := C.isCompact.image Units.continuous_val
  have hDm : MeasurableSet D := hDc.isClosed.measurableSet
  have hpreD : (fun t : Ga K => (t : Matrix (Fin 2) (Fin 2) (Kinf K))) ⁻¹' D = (C : Set (Ga K)) :=
    Set.preimage_image_eq _ Units.val_injective
  have hCD : τa C = s * ρ D := by
    have h := congrArg (fun m : Measure (Matrix (Fin 2) (Fin 2) (Kinf K)) => m D) hmap
    rw [Measure.map_apply (measurable_valA K) hDm, hpreD, Measure.smul_apply, smul_eq_mul] at h
    exact h
  rw [hs] at hCD
  by_cases hρ : ρ D = 0
  · rw [hρ, mul_zero] at hCD
    exact hpos.ne' hCD
  · rw [ENNReal.top_mul hρ] at hCD
    exact hlt.ne hCD

end Finite

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem mem_O_iff (x : v.adicCompletion K) : x ∈ v.adicCompletionIntegers K ↔ Valued.v x ≤ 1 :=
  HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

private theorem _root_.AutomorphicForm.WeilConstant.norm_lt_one_iff (x : v.adicCompletion K) : ‖x‖ < 1 ↔ Valued.v x < 1 :=
  Valued.toNormedField.norm_lt_one_iff

p2m_export "AutomorphicForm.WeilConstant" "norm_lt_one_iff"
private theorem _root_.AutomorphicForm.WeilConstant.norm_le_one_iff (x : v.adicCompletion K) : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff

p2m_export "AutomorphicForm.WeilConstant" "norm_le_one_iff"

theorem mem_localIntegralSet_of (k : GL (Fin 2) (v.adicCompletion K))
    (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K)
    (hdet : (((Matrix.GeneralLinearGroup.det k)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
      v.adicCompletionIntegers K) :
    k ∈ AutomorphicForm.localIntegralSet K v := by
  refine ⟨hk, fun i j => ?_⟩
  have hinv : ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      (((Matrix.GeneralLinearGroup.det k)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) •
        (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def]
    congr 1
    have : (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det =
        ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion K)ˣ) : v.adicCompletion K) :=
      (Matrix.GeneralLinearGroup.val_det_apply k).symm
    rw [this, Ring.inverse_unit]
  rw [hinv, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_two]
  refine mul_mem hdet ?_
  fin_cases i <;> fin_cases j <;> simp [hk]

theorem det_mem_of_mem {k : GL (Fin 2) (v.adicCompletion K)} (hk : k ∈ AutomorphicForm.localIntegralSet K v) :
    ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      (((Matrix.GeneralLinearGroup.det k)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
        v.adicCompletionIntegers K := by
  obtain ⟨h1, h2⟩ := hk
  constructor
  · rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    exact sub_mem (mul_mem (h1 0 0) (h1 1 1)) (mul_mem (h1 0 1) (h1 1 0))
  · rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    exact sub_mem (mul_mem (h2 0 0) (h2 1 1)) (mul_mem (h2 0 1) (h2 1 0))

theorem not_both_lt_of_mem {k : GL (Fin 2) (v.adicCompletion K)} (hk : k ∈ AutomorphicForm.localIntegralSet K v) :
    ¬ (‖(k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ < 1 ∧
      ‖(k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0‖ < 1) := by
  rintro ⟨ha, hc⟩
  rw [norm_lt_one_iff] at ha hc
  obtain ⟨hd, hdi⟩ := det_mem_of_mem K v hk
  rw [mem_O_iff] at hd hdi
  have h1 := hk.1
  have hlt : Valued.v ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion K)ˣ) : v.adicCompletion K) < 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · rw [Valuation.map_mul]
      calc Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0) *
            Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1)
          ≤ Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0) * 1 := by
            gcongr; exact (mem_O_iff K v _).1 (h1 1 1)
        _ < 1 := by rw [mul_one]; exact ha
    · rw [Valuation.map_mul]
      calc Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1) *
            Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0)
          ≤ 1 * Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0) := by
            gcongr; exact (mem_O_iff K v _).1 (h1 0 1)
        _ < 1 := by rw [one_mul]; exact hc
  have hone : Valued.v ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion K)ˣ) : v.adicCompletion K) *
      Valued.v (((Matrix.GeneralLinearGroup.det k)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [← Valuation.map_mul, Units.mul_inv, Valuation.map_one]
  have : Valued.v ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion K)ˣ) : v.adicCompletion K) *
      Valued.v (((Matrix.GeneralLinearGroup.det k)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) < 1 :=
    mul_lt_one_of_lt_of_le hlt hdi
  rw [hone] at this
  exact lt_irrefl _ this

theorem norm_eq_one_of_mem_of_inv_mem {x : (v.adicCompletion K)ˣ}
    (h1 : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (h2 : ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    ‖(x : v.adicCompletion K)‖ = 1 := by
  rw [mem_O_iff, ← norm_le_one_iff] at h1 h2
  have hmul : ‖(x : v.adicCompletion K)‖ * ‖((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1 := by
    rw [← norm_mul, Units.mul_inv, norm_one]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = ‖(x : v.adicCompletion K)‖ * ‖((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ := hmul.symm
    _ ≤ ‖(x : v.adicCompletion K)‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖(x : v.adicCompletion K)‖ := mul_one _

theorem coe_mul_unipotentGL2 {R : Type*} [CommRing R] (k : GL (Fin 2) R) (r : R) (i : Fin 2) :
    ((k * AutomorphicForm.unipotentGL2 r : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 0 =
        (k : Matrix (Fin 2) (Fin 2) R) i 0 ∧
      ((k * AutomorphicForm.unipotentGL2 r : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 1 =
        (k : Matrix (Fin 2) (Fin 2) R) i 0 * r + (k : Matrix (Fin 2) (Fin 2) R) i 1 := by
  simp [Units.val_mul, AutomorphicForm.unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem map_unipotentGL2 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map f (AutomorphicForm.unipotentGL2 x) = AutomorphicForm.unipotentGL2 (f x) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, AutomorphicForm.unipotentGL2_coe, AutomorphicForm.unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem exists_mul_unipotentGL2_mem (k : GL (Fin 2) (v.adicCompletion K))
    (h0 : (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 ∈ v.adicCompletionIntegers K)
    (h1 : (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 ∈ v.adicCompletionIntegers K)
    (hprim : ¬ (‖(k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ < 1 ∧
      ‖(k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0‖ < 1))
    (hdet : ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
      v.adicCompletionIntegers K)
    (hdet' : (((Matrix.GeneralLinearGroup.det k)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
      v.adicCompletionIntegers K) :
    ∃ r : v.adicCompletion K, k * AutomorphicForm.unipotentGL2 r ∈ AutomorphicForm.localIntegralSet K v ∧
      ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 ∈ v.adicCompletionIntegers K →
        (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 ∈ v.adicCompletionIntegers K →
          r ∈ v.adicCompletionIntegers K) := by
  set a := (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 with ha
  set b := (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 with hb
  set c := (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 with hc
  set d := (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 with hd
  set δ : (v.adicCompletion K)ˣ := Matrix.GeneralLinearGroup.det k with hδ
  have hδval : (δ : v.adicCompletion K) = a * d - b * c := by
    rw [hδ, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hδ1 : Valued.v (δ : v.adicCompletion K) ≤ 1 := (mem_O_iff K v _).1 hdet

  have hdetn : ∀ r : v.adicCompletion K,
      Matrix.GeneralLinearGroup.det (k * AutomorphicForm.unipotentGL2 r) = δ := by
    intro r
    rw [map_mul]
    have : Matrix.GeneralLinearGroup.det (AutomorphicForm.unipotentGL2 r : GL (Fin 2) (v.adicCompletion K)) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, AutomorphicForm.unipotentGL2_coe, Matrix.det_fin_two_of]
      simp
    rw [this, mul_one]

  have key : ∀ r : v.adicCompletion K, a * r + b ∈ v.adicCompletionIntegers K →
      c * r + d ∈ v.adicCompletionIntegers K →
        k * AutomorphicForm.unipotentGL2 r ∈ AutomorphicForm.localIntegralSet K v := by
    intro r hr0 hr1
    refine mem_localIntegralSet_of K v _ (fun i j => ?_) (by rw [hdetn]; exact hdet')
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
    · rw [(coe_mul_unipotentGL2 k r 0).1]; exact h0
    · rw [(coe_mul_unipotentGL2 k r 0).2]; exact hr0
    · rw [(coe_mul_unipotentGL2 k r 1).1]; exact h1
    · rw [(coe_mul_unipotentGL2 k r 1).2]; exact hr1
  by_cases hau : ‖a‖ < 1
  ·
    have hcu : ¬ ‖c‖ < 1 := fun h => hprim ⟨hau, h⟩
    have hc1 : Valued.v c = 1 :=
      le_antisymm ((mem_O_iff K v c).1 h1) (not_lt.1 (by rwa [← norm_lt_one_iff]))
    have hc0 : c ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hc1; exact zero_ne_one hc1
    refine ⟨-(d / c), key _ ?_ ?_, fun _ hdint => ?_⟩
    · have : a * -(d / c) + b = -(δ : v.adicCompletion K) / c := by rw [hδval]; field_simp; ring
      rw [this, mem_O_iff, Valuation.map_div, Valuation.map_neg, hc1, div_one]
      exact hδ1
    · have : c * -(d / c) + d = 0 := by field_simp; ring
      rw [this]; exact zero_mem _
    · rw [mem_O_iff, Valuation.map_neg, Valuation.map_div, hc1, div_one]
      exact (mem_O_iff K v d).1 hdint
  ·
    have ha1 : Valued.v a = 1 :=
      le_antisymm ((mem_O_iff K v a).1 h0) (not_lt.1 (by rwa [← norm_lt_one_iff]))
    have ha0 : a ≠ 0 := by intro h; rw [h, Valuation.map_zero] at ha1; exact zero_ne_one ha1
    refine ⟨-(b / a), key _ ?_ ?_, fun hbint _ => ?_⟩
    · have : a * -(b / a) + b = 0 := by field_simp; ring
      rw [this]; exact zero_mem _
    · have : c * -(b / a) + d = (δ : v.adicCompletion K) / a := by rw [hδval]; field_simp; ring
      rw [this, mem_O_iff, Valuation.map_div, ha1, div_one]
      exact hδ1
    · rw [mem_O_iff, Valuation.map_neg, Valuation.map_div, ha1, div_one]
      exact (mem_O_iff K v b).1 hbint

end Local

section Global

variable (K : Type) [Field K] [NumberField K]

abbrev arch (g : Gp K) : Ga K := AdelicLevel.glArch (𝓞 K) K g

abbrev locAt (g : Gp K) (v : HeightOneSpectrum (𝓞 K)) : GL (Fin 2) (v.adicCompletion K) :=
  AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g)

theorem arch_apply (g : Gp K) (i j : Fin 2) :
    (arch K g : Matrix (Fin 2) (Fin 2) (Kinf K)) i j = ((g : Matrix (Fin 2) (Fin 2) (Ad K)) i j).1 := rfl

theorem locAt_apply (g : Gp K) (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2) :
    (locAt K g v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      (((g : Matrix (Fin 2) (Fin 2) (Ad K)) i j).2 : Adf K) v := rfl

theorem det_arch (g : Gp K) :
    ((Matrix.GeneralLinearGroup.det (arch K g) : (Kinf K)ˣ) : Kinf K) =
      ((Matrix.GeneralLinearGroup.det g : (Ad K)ˣ) : Ad K).1 :=
  congrArg Units.val (Matrix.GeneralLinearGroup.map_det (AdelicLevel.adeleArch (𝓞 K) K) g)

theorem det_locAt (g : Gp K) (v : HeightOneSpectrum (𝓞 K)) :
    ((Matrix.GeneralLinearGroup.det (locAt K g v) : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      (((Matrix.GeneralLinearGroup.det g : (Ad K)ˣ) : Ad K).2 : Adf K) v := by
  have h1 := congrArg Units.val
    (Matrix.GeneralLinearGroup.map_det (AdelicLevel.finAdeleEval (𝓞 K) K v) (AdelicLevel.glFin (𝓞 K) K g))
  have h2 := congrArg Units.val (Matrix.GeneralLinearGroup.map_det (AdelicLevel.adeleFin (𝓞 K) K) g)
  rw [Units.coe_map] at h1 h2
  simp only [MonoidHom.coe_coe] at h1 h2
  rw [locAt, AdelicLevel.finComponent, h1, AdelicLevel.glFin, h2]
  rfl

theorem det_inv_locAt (g : Gp K) (v : HeightOneSpectrum (𝓞 K)) :
    (((Matrix.GeneralLinearGroup.det (locAt K g v))⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ((((Matrix.GeneralLinearGroup.det g)⁻¹ : (Ad K)ˣ) : Ad K).2 : Adf K) v := by
  rw [locAt, ← map_inv, ← map_inv, ← map_inv, ← map_inv]
  exact det_locAt K g⁻¹ v

theorem glFin_mul_unipotentGL2 (g : Gp K) (t : Ad K) :
    AdelicLevel.glFin (𝓞 K) K (g * AutomorphicForm.unipotentGL2 t) =
      AdelicLevel.glFin (𝓞 K) K g * AutomorphicForm.unipotentGL2 t.2 := by
  rw [map_mul, AdelicLevel.glFin, map_unipotentGL2]
  rfl

theorem arch_mul_unipotentGL2 (g : Gp K) (t : Ad K) :
    arch K (g * AutomorphicForm.unipotentGL2 t) = arch K g * AutomorphicForm.unipotentGL2 t.1 := by
  rw [arch, map_mul, AdelicLevel.glArch, map_unipotentGL2]
  rfl

theorem finComponent_mul_unipotentGL2 (h : GL (Fin 2) (Adf K)) (s : Adf K) (v : HeightOneSpectrum (𝓞 K)) :
    AdelicLevel.finComponent (𝓞 K) K v (h * AutomorphicForm.unipotentGL2 s) =
      AdelicLevel.finComponent (𝓞 K) K v h * AutomorphicForm.unipotentGL2 (s v) := by
  rw [map_mul, AdelicLevel.finComponent, map_unipotentGL2]
  rfl

def Ufin : Set (Gp K) := {g | AdelicLevel.glFin (𝓞 K) K g ∈ AutomorphicForm.unitFinSet K}

theorem isOpen_Ufin : IsOpen (Ufin K) :=
  (AutomorphicForm.isOpen_unitFinSet K).preimage (AdelicLevel.continuous_glFin (𝓞 K) K)

variable {K}

theorem mul_mem_unitFinSet_iff {h : GL (Fin 2) (Adf K)} (hh : h ∈ AutomorphicForm.unitFinSet K)
    (u : GL (Fin 2) (Adf K)) : h * u ∈ AutomorphicForm.unitFinSet K ↔ u ∈ AutomorphicForm.unitFinSet K := by
  rw [AutomorphicForm.unitFinSet_eq_finiteIntegralGL2] at hh ⊢
  exact Subgroup.mul_mem_cancel_left _ hh

theorem unipotentGL2_mem_unitFinSet_iff (s : Adf K) :
    (AutomorphicForm.unipotentGL2 s : GL (Fin 2) (Adf K)) ∈ AutomorphicForm.unitFinSet K ↔
      ∀ v : HeightOneSpectrum (𝓞 K), s v ∈ v.adicCompletionIntegers K := by
  constructor
  · intro h v
    have hv := (h v).1 0 1
    rw [AdelicLevel.finComponent, map_unipotentGL2, AutomorphicForm.unipotentGL2_coe] at hv
    simp at hv
    exact hv
  · intro h v
    rw [AdelicLevel.finComponent, map_unipotentGL2]
    refine mem_localIntegralSet_of K v _ (fun i j => ?_) ?_
    · rw [AutomorphicForm.unipotentGL2_coe]
      fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]
      exact h v
    · have : Matrix.GeneralLinearGroup.det
          (AutomorphicForm.unipotentGL2 (AdelicLevel.finAdeleEval (𝓞 K) K v s) : GL (Fin 2) (v.adicCompletion K)) = 1 := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_det_apply, AutomorphicForm.unipotentGL2_coe, Matrix.det_fin_two_of]
        simp
      rw [this, inv_one, Units.val_one]
      exact one_mem _

variable (K)

def Good : Set (Gp K) := {g | ∃ t : Ad K, g * AutomorphicForm.unipotentGL2 t ∈ Ufin K}

theorem isOpen_Good : IsOpen (Good K) := by
  have h : Good K = ⋃ t : Ad K, (fun g : Gp K => g * AutomorphicForm.unipotentGL2 t) ⁻¹' Ufin K := by
    ext g; simp [Good]
  rw [h]
  exact isOpen_iUnion fun t => (isOpen_Ufin K).preimage (continuous_id.mul continuous_const)

theorem measurableSet_Good : MeasurableSet (Good K) := (isOpen_Good K).measurableSet

theorem mul_unipotentGL2_mem_Good_iff (g : Gp K) (x : Ad K) :
    g * AutomorphicForm.unipotentGL2 x ∈ Good K ↔ g ∈ Good K := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨x + t, ?_⟩
    rwa [AutomorphicForm.unipotentGL2_add, ← mul_assoc]
  · rintro ⟨t, ht⟩
    refine ⟨-x + t, ?_⟩
    rwa [AutomorphicForm.unipotentGL2_add, ← mul_assoc, mul_assoc g, ← AutomorphicForm.unipotentGL2_add,
      add_neg_cancel, AutomorphicForm.unipotentGL2_zero, mul_one]

theorem mem_Good_of_mem_Ufin {g : Gp K} (hg : g ∈ Ufin K) : g ∈ Good K :=
  ⟨0, by rwa [AutomorphicForm.unipotentGL2_zero, mul_one]⟩

theorem mem_Good_of (g : Gp K)
    (hint : ∀ v : HeightOneSpectrum (𝓞 K),
      (((g : Matrix (Fin 2) (Fin 2) (Ad K)) 0 0).2 : Adf K) v ∈ v.adicCompletionIntegers K ∧
      (((g : Matrix (Fin 2) (Fin 2) (Ad K)) 1 0).2 : Adf K) v ∈ v.adicCompletionIntegers K)
    (hprim : ∀ v : HeightOneSpectrum (𝓞 K),
      ¬ (‖(((g : Matrix (Fin 2) (Fin 2) (Ad K)) 0 0).2 : Adf K) v‖ < 1 ∧
        ‖(((g : Matrix (Fin 2) (Fin 2) (Ad K)) 1 0).2 : Adf K) v‖ < 1))
    (hdet : ∀ v : HeightOneSpectrum (𝓞 K),
      (((Matrix.GeneralLinearGroup.det g : (Ad K)ˣ) : Ad K).2 : Adf K) v ∈ v.adicCompletionIntegers K ∧
      ((((Matrix.GeneralLinearGroup.det g)⁻¹ : (Ad K)ˣ) : Ad K).2 : Adf K) v ∈ v.adicCompletionIntegers K) :
    g ∈ Good K := by

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ r : v.adicCompletion K,
      locAt K g v * AutomorphicForm.unipotentGL2 r ∈ AutomorphicForm.localIntegralSet K v ∧
      ((((g : Matrix (Fin 2) (Fin 2) (Ad K)) 0 1).2 : Adf K) v ∈ v.adicCompletionIntegers K →
        (((g : Matrix (Fin 2) (Fin 2) (Ad K)) 1 1).2 : Adf K) v ∈ v.adicCompletionIntegers K →
          r ∈ v.adicCompletionIntegers K) := by
    intro v
    have h := exists_mul_unipotentGL2_mem K v (locAt K g v)
      (by rw [locAt_apply]; exact (hint v).1) (by rw [locAt_apply]; exact (hint v).2)
      (by rw [locAt_apply, locAt_apply]; exact hprim v)
      (by rw [det_locAt]; exact (hdet v).1) (by rw [det_inv_locAt]; exact (hdet v).2)
    simpa only [locAt_apply] using h
  choose r hr hrint using hloc

  have hev : ∀ᶠ v in Filter.cofinite, r v ∈ v.adicCompletionIntegers K := by
    have h01 : ∀ᶠ v in Filter.cofinite, (((g : Matrix (Fin 2) (Fin 2) (Ad K)) 0 1).2 : Adf K) v ∈
        v.adicCompletionIntegers K := (((g : Matrix (Fin 2) (Fin 2) (Ad K)) 0 1).2).2
    have h11 : ∀ᶠ v in Filter.cofinite, (((g : Matrix (Fin 2) (Fin 2) (Ad K)) 1 1).2 : Adf K) v ∈
        v.adicCompletionIntegers K := (((g : Matrix (Fin 2) (Fin 2) (Ad K)) 1 1).2).2
    filter_upwards [h01, h11] with v hv0 hv1
    exact hrint v hv0 hv1
  let tf : Adf K :=
    (⟨r, hev⟩ : RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite)
  have htf : ∀ v, tf v = r v := fun v => rfl
  refine ⟨((0 : Kinf K), tf), fun v => ?_⟩
  rw [glFin_mul_unipotentGL2, finComponent_mul_unipotentGL2]
  show locAt K g v * AutomorphicForm.unipotentGL2 (tf v) ∈ _
  rw [htf]
  exact hr v

def Wset (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K) : Set (Gp K) :=
  {g | y (arch K g : Matrix (Fin 2) (Fin 2) (Kinf K)) ∈ cube K ∧ g ∈ Ufin K}

def W (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K) (g : Gp K) : ℝ≥0∞ :=
  (Wset K y).indicator (fun _ => (1 : ℝ≥0∞)) g

theorem measurable_archMat : Measurable fun g : Gp K => (arch K g : Matrix (Fin 2) (Fin 2) (Kinf K)) :=
  (Units.continuous_val.comp (AdelicLevel.continuous_glArch (𝓞 K) K)).measurable

theorem measurableSet_Wset {y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K} (hy : Measurable y) :
    MeasurableSet (Wset K y) := by
  have h : Wset K y = ((fun g : Gp K => y (arch K g : Matrix (Fin 2) (Fin 2) (Kinf K))) ⁻¹' cube K) ∩ Ufin K := by
    ext g; simp [Wset]
  rw [h]
  exact ((hy.comp (measurable_archMat K)) (measurableSet_cube K)).inter (isOpen_Ufin K).measurableSet

theorem measurable_W {y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K} (hy : Measurable y) : Measurable (W K y) :=
  measurable_const.indicator (measurableSet_Wset K hy)

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]

def adOf (a : Kinf K) (b : Adf K) : Ad K := (a, b)

theorem W_mul_unipotentGL2_eq (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K)
    (hy1 : ∀ (g : Ga K) (x : Kinf K),
      y ((g * AutomorphicForm.unipotentGL2 x : Ga K) : Matrix (Fin 2) (Fin 2) (Kinf K)) =
        y (g : Matrix (Fin 2) (Fin 2) (Kinf K)) + eK K x)
    {g : Gp K} {t : Ad K} (ht : g * AutomorphicForm.unipotentGL2 t ∈ Ufin K) (x : Ad K) :
    W K y (g * AutomorphicForm.unipotentGL2 x) =
      ((fun z : Ad K => adOf K ((eK K).symm (y (arch K g : Matrix (Fin 2) (Fin 2) (Kinf K)))) (-t.2) + z) ⁻¹'
          Ebox K).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  have ht' : AdelicLevel.glFin (𝓞 K) K (g * AutomorphicForm.unipotentGL2 t) ∈ AutomorphicForm.unitFinSet K := ht

  have hfin : g * AutomorphicForm.unipotentGL2 x ∈ Ufin K ↔
      ∀ v : HeightOneSpectrum (𝓞 K), (x.2 - t.2 : Adf K) v ∈ v.adicCompletionIntegers K := by
    have hx : g * AutomorphicForm.unipotentGL2 x =
        g * AutomorphicForm.unipotentGL2 t * AutomorphicForm.unipotentGL2 (x - t) := by
      rw [mul_assoc, ← AutomorphicForm.unipotentGL2_add, add_sub_cancel]
    rw [hx]
    unfold Ufin
    rw [Set.mem_setOf_eq, glFin_mul_unipotentGL2, mul_mem_unitFinSet_iff ht', unipotentGL2_mem_unitFinSet_iff]
    exact Iff.rfl
  have harch : y (arch K (g * AutomorphicForm.unipotentGL2 x) : Matrix (Fin 2) (Fin 2) (Kinf K)) =
      eK K (((eK K).symm (y (arch K g : Matrix (Fin 2) (Fin 2) (Kinf K)))) + x.1) := by
    rw [arch_mul_unipotentGL2, hy1, map_add, RingEquiv.apply_symm_apply, add_comm]
  have hiff : g * AutomorphicForm.unipotentGL2 x ∈ Wset K y ↔
      (adOf K ((eK K).symm (y (arch K g : Matrix (Fin 2) (Fin 2) (Kinf K)))) (-t.2) + x) ∈ Ebox K := by
    rw [mem_Ebox_iff]
    change y (arch K (g * AutomorphicForm.unipotentGL2 x) : Matrix (Fin 2) (Fin 2) (Kinf K)) ∈ cube K ∧
        g * AutomorphicForm.unipotentGL2 x ∈ Ufin K ↔
      eK K ((eK K).symm (y (arch K g : Matrix (Fin 2) (Fin 2) (Kinf K))) + x.1) ∈ cube K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), ((-t.2 + x.2 : Adf K)) v ∈ v.adicCompletionIntegers K
    rw [harch, hfin, neg_add_eq_sub]
  unfold W
  by_cases hmem : g * AutomorphicForm.unipotentGL2 x ∈ Wset K y
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show x ∈ _ from hiff.1 hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show x ∉ _ from fun h => hmem (hiff.2 h))]

theorem lintegral_W_of_mem_Good (μ : Measure (Ad K)) [μ.IsAddLeftInvariant]
    (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K)
    (hy1 : ∀ (g : Ga K) (x : Kinf K),
      y ((g * AutomorphicForm.unipotentGL2 x : Ga K) : Matrix (Fin 2) (Fin 2) (Kinf K)) =
        y (g : Matrix (Fin 2) (Fin 2) (Kinf K)) + eK K x)
    {g : Gp K} (hg : g ∈ Good K) :
    ∫⁻ x, W K y (g * AutomorphicForm.unipotentGL2 x) ∂μ = μ (Ebox K) := by
  obtain ⟨t, ht⟩ := hg
  simp_rw [W_mul_unipotentGL2_eq K y hy1 ht]
  rw [lintegral_indicator_const ((measurable_const_add _) (measurableSet_Ebox K)), one_mul,
    measure_preimage_add]

theorem W_eq_zero_of_not_mem_Good (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K) {g : Gp K} (hg : g ∉ Good K)
    (x : Ad K) : W K y (g * AutomorphicForm.unipotentGL2 x) = 0 := by
  unfold W
  refine Set.indicator_of_notMem (fun h => hg ?_) _
  exact ⟨x, h.2⟩

def wSharp (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K) (a : ℝ≥0∞) (w₀ : Gp K → ℝ≥0∞) (g : Gp K) : ℝ≥0∞ :=
  if g ∈ Good K then a⁻¹ * W K y g else w₀ g

theorem measurable_wSharp {y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K} (hy : Measurable y) (a : ℝ≥0∞)
    {w₀ : Gp K → ℝ≥0∞} (hw₀ : Measurable w₀) : Measurable (wSharp K y a w₀) := by
  unfold wSharp
  exact Measurable.ite (measurableSet_Good K) (measurable_const.mul (measurable_W K hy)) hw₀

theorem lintegral_wSharp (μ : Measure (Ad K)) [μ.IsAddLeftInvariant]
    (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K) (hy : Measurable y)
    (hy1 : ∀ (g : Ga K) (x : Kinf K),
      y ((g * AutomorphicForm.unipotentGL2 x : Ga K) : Matrix (Fin 2) (Fin 2) (Kinf K)) =
        y (g : Matrix (Fin 2) (Fin 2) (Kinf K)) + eK K x)
    (ha0 : μ (Ebox K) ≠ 0) (hatop : μ (Ebox K) ≠ ⊤)
    {w₀ : Gp K → ℝ≥0∞} (hw₀ : ∀ g : Gp K, ∫⁻ x, w₀ (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1) (g : Gp K) :
    ∫⁻ x, wSharp K y (μ (Ebox K)) w₀ (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1 := by
  by_cases hg : g ∈ Good K
  · have h : ∀ x : Ad K, wSharp K y (μ (Ebox K)) w₀ (g * AutomorphicForm.unipotentGL2 x) =
        (μ (Ebox K))⁻¹ * W K y (g * AutomorphicForm.unipotentGL2 x) := fun x => by
      rw [wSharp, if_pos ((mul_unipotentGL2_mem_Good_iff K g x).2 hg)]
    simp_rw [h]
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 ha0), lintegral_W_of_mem_Good K μ y hy1 hg,
      ENNReal.inv_mul_cancel ha0 hatop]
  · have h : ∀ x : Ad K, wSharp K y (μ (Ebox K)) w₀ (g * AutomorphicForm.unipotentGL2 x) =
        w₀ (g * AutomorphicForm.unipotentGL2 x) := fun x => by
      rw [wSharp, if_neg (fun h => hg ((mul_unipotentGL2_mem_Good_iff K g x).1 h))]
    simp_rw [h]
    exact hw₀ g

end Global

section TauSide

variable (K : Type) [Field K] [NumberField K]

def Tset (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K) : Set (Ga K) :=
  {h | y (h : Matrix (Fin 2) (Fin 2) (Kinf K)) ∈ cube K ∧
    (∀ i : Fin 2, eK K ((h : Matrix (Fin 2) (Fin 2) (Kinf K)) i 0) ∈ cube K) ∧
    ∀ w : InfinitePlace K,
      ‖((Matrix.GeneralLinearGroup.det h : (Kinf K)ˣ) : Kinf K) w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)}

def Wa (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K) (h : Ga K) : ℝ≥0∞ :=
  (Tset K y).indicator (fun h => ENNReal.ofReal ‖((Matrix.GeneralLinearGroup.det h : (Kinf K)ˣ) : Kinf K)‖) h

def Wp (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K) (g : Gp K) : ℝ≥0∞ :=
  Wa K y (arch K g) * (Ufin K).indicator (fun _ => (1 : ℝ≥0∞)) g

theorem continuous_normKinf : Continuous fun x : Kinf K => ‖x‖ := by
  show Continuous fun x : Kinf K => ∏ v : InfinitePlace K, ‖x v‖ ^ v.mult
  exact continuous_finsetProd _ fun v _ => ((continuous_apply v).norm).pow _

theorem continuous_detA : Continuous fun h : Ga K => ((Matrix.GeneralLinearGroup.det h : (Kinf K)ˣ) : Kinf K) := by
  have : (fun h : Ga K => ((Matrix.GeneralLinearGroup.det h : (Kinf K)ˣ) : Kinf K)) =
      fun h : Ga K => (h : Matrix (Fin 2) (Fin 2) (Kinf K)).det := by
    funext h; rw [Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Units.continuous_val.matrix_det

theorem measurableSet_Tset {y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K} (hy : Measurable y) :
    MeasurableSet (Tset K y) := by
  have h : Tset K y =
      ((fun h : Ga K => y (h : Matrix (Fin 2) (Fin 2) (Kinf K))) ⁻¹' cube K) ∩
        ((⋂ i : Fin 2, (fun h : Ga K => eK K ((h : Matrix (Fin 2) (Fin 2) (Kinf K)) i 0)) ⁻¹' cube K) ∩
          ⋂ w : InfinitePlace K,
            (fun h : Ga K => ‖((Matrix.GeneralLinearGroup.det h : (Kinf K)ˣ) : Kinf K) w‖) ⁻¹'
              Set.Icc (1 : ℝ) (Real.exp 1)) := by
    ext h
    simp only [Tset, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter]
  rw [h]
  refine ((hy.comp (measurable_valA K)) (measurableSet_cube K)).inter
    ((MeasurableSet.iInter fun i => ?_).inter (MeasurableSet.iInter fun w => ?_))
  · exact ((continuous_eK K).comp (Units.continuous_val.matrix_elem i 0)).measurable (measurableSet_cube K)
  · exact (continuous_norm.comp ((continuous_apply w).comp (continuous_detA K))).measurable measurableSet_Icc

theorem measurable_Wa {y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K} (hy : Measurable y) : Measurable (Wa K y) := by
  unfold Wa
  refine Measurable.indicator ?_ (measurableSet_Tset K hy)
  exact ENNReal.measurable_ofReal.comp ((continuous_normKinf K).comp (continuous_detA K)).measurable

theorem measurable_Wp {y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K} (hy : Measurable y) : Measurable (Wp K y) := by
  unfold Wp
  exact ((measurable_Wa K hy).comp (AdelicLevel.continuous_glArch (𝓞 K) K).measurable).mul
    (measurable_const.indicator (isOpen_Ufin K).measurableSet)

theorem Wa_ne_top (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K) (h : Ga K) : Wa K y h ≠ ⊤ := by
  unfold Wa
  by_cases hh : h ∈ Tset K y
  · rw [Set.indicator_of_mem hh]; exact ENNReal.ofReal_ne_top
  · rw [Set.indicator_of_notMem hh]; exact ENNReal.zero_ne_top

theorem Wp_ne_top (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K) (g : Gp K) : Wp K y g ≠ ⊤ := by
  unfold Wp
  refine ENNReal.mul_ne_top (Wa_ne_top K y _) ?_
  by_cases hg : g ∈ Ufin K
  · rw [Set.indicator_of_mem hg]; exact ENNReal.one_ne_top
  · rw [Set.indicator_of_notMem hg]; exact ENNReal.zero_ne_top

theorem facts_of_mem_Ufin {g : Gp K} (hg : g ∈ Ufin K) :
    (∀ v : HeightOneSpectrum (𝓞 K),
      (((g : Matrix (Fin 2) (Fin 2) (Ad K)) 0 0).2 : Adf K) v ∈ v.adicCompletionIntegers K ∧
      (((g : Matrix (Fin 2) (Fin 2) (Ad K)) 1 0).2 : Adf K) v ∈ v.adicCompletionIntegers K) ∧
    (∀ v : HeightOneSpectrum (𝓞 K),
      ¬ (‖(((g : Matrix (Fin 2) (Fin 2) (Ad K)) 0 0).2 : Adf K) v‖ < 1 ∧
        ‖(((g : Matrix (Fin 2) (Fin 2) (Ad K)) 1 0).2 : Adf K) v‖ < 1)) ∧
    (∀ v : HeightOneSpectrum (𝓞 K),
      (((Matrix.GeneralLinearGroup.det g : (Ad K)ˣ) : Ad K).2 : Adf K) v ∈ v.adicCompletionIntegers K ∧
      ((((Matrix.GeneralLinearGroup.det g)⁻¹ : (Ad K)ˣ) : Ad K).2 : Adf K) v ∈ v.adicCompletionIntegers K) ∧
    ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) =
      ENNReal.ofReal ‖((Matrix.GeneralLinearGroup.det (arch K g) : (Kinf K)ˣ) : Kinf K)‖ := by
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), locAt K g v ∈ AutomorphicForm.localIntegralSet K v := fun v => hg v
  have hdet : ∀ v : HeightOneSpectrum (𝓞 K),
      (((Matrix.GeneralLinearGroup.det g : (Ad K)ˣ) : Ad K).2 : Adf K) v ∈ v.adicCompletionIntegers K ∧
      ((((Matrix.GeneralLinearGroup.det g)⁻¹ : (Ad K)ˣ) : Ad K).2 : Adf K) v ∈ v.adicCompletionIntegers K := by
    intro v
    have h := det_mem_of_mem K v (hloc v)
    rw [det_locAt, det_inv_locAt] at h
    exact h
  refine ⟨fun v => ⟨?_, ?_⟩, fun v => ?_, hdet, ?_⟩
  · have h := (hloc v).1 0 0
    rw [locAt_apply] at h
    exact h
  · have h := (hloc v).1 1 0
    rw [locAt_apply] at h
    exact h
  · have h := not_both_lt_of_mem K v (hloc v)
    rw [locAt_apply, locAt_apply] at h
    exact h
  have hone : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖(((Matrix.GeneralLinearGroup.det g : (Ad K)ˣ) : Ad K).2 : Adf K) v‖ = 1 := by
    intro v
    have h := norm_eq_one_of_mem_of_inv_mem K v (x := Matrix.GeneralLinearGroup.det (locAt K g v))
      (by rw [det_locAt]; exact (hdet v).1) (by rw [det_inv_locAt]; exact (hdet v).2)
    rw [det_locAt] at h
    exact h
  rw [NumberField.TateGlobal.ideleNorm,
    NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm K (Matrix.GeneralLinearGroup.det g),
    finprod_eq_one_of_forall_eq_one hone, mul_one, det_arch, InfiniteAdeleRing.norm_def]

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

theorem wSharp_mul_Ψt (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K) (a : ℝ≥0∞) (w₀ : Gp K → ℝ≥0∞) (g : Gp K) :
    wSharp K y a w₀ g *
        Ψt K (fun i => (g : Matrix (Fin 2) (Fin 2) (Ad K)) i 0, Matrix.GeneralLinearGroup.det g) =
      a⁻¹ * Wp K y g := by
  by_cases hU : g ∈ Ufin K
  · have hG : g ∈ Good K := mem_Good_of_mem_Ufin K hU
    rw [wSharp, if_pos hG, Wp, Set.indicator_of_mem hU, mul_one, mul_assoc]
    congr 1
    obtain ⟨F1, F2, F3, F4⟩ := facts_of_mem_Ufin K hU
    by_cases hT : arch K g ∈ Tset K y
    · have hW : g ∈ Wset K y := ⟨hT.1, hU⟩
      have hSh : Matrix.GeneralLinearGroup.det g ∈ Sh K := by
        refine ⟨F3, fun w => ?_⟩
        have h := hT.2.2 w
        rwa [det_arch] at h
      have hP : ((fun i => (g : Matrix (Fin 2) (Fin 2) (Ad K)) i 0), Matrix.GeneralLinearGroup.det g) ∈
          P1 K ×ˢ Sh K :=
        ⟨⟨⟨hT.2.1 0, hT.2.1 1⟩, F1, F2⟩, hSh⟩
      rw [W, Ψt, Wa, Set.indicator_of_mem hW, Set.indicator_of_mem hP, Set.indicator_of_mem hT, one_mul, F4]
    · rw [Wa, Set.indicator_of_notMem hT]
      by_cases hyc : y (arch K g : Matrix (Fin 2) (Fin 2) (Kinf K)) ∈ cube K
      · have hP : ((fun i => (g : Matrix (Fin 2) (Fin 2) (Ad K)) i 0), Matrix.GeneralLinearGroup.det g) ∉
            P1 K ×ˢ Sh K := by
          rintro ⟨⟨hcol, -, -⟩, hSh⟩
          refine hT ⟨hyc, fun i => ?_, fun w => ?_⟩
          · fin_cases i
            · exact hcol.1
            · exact hcol.2
          · rw [det_arch]; exact hSh.2 w
        rw [Ψt, Set.indicator_of_notMem hP, mul_zero]
      · have hW : g ∉ Wset K y := fun h => hyc h.1
        rw [W, Set.indicator_of_notMem hW, zero_mul]
  · rw [Wp, Set.indicator_of_notMem hU, mul_zero, mul_zero]
    by_cases hG : g ∈ Good K
    · rw [wSharp, if_pos hG, W, Set.indicator_of_notMem (fun h => hU h.2), mul_zero, zero_mul]
    · rw [wSharp, if_neg hG]
      have hP : ((fun i => (g : Matrix (Fin 2) (Fin 2) (Ad K)) i 0), Matrix.GeneralLinearGroup.det g) ∉
          P1 K ×ˢ Sh K := fun h => hG (mem_Good_of K g h.1.2.1 h.1.2.2 h.2.1)
      rw [Ψt, Set.indicator_of_notMem hP, mul_zero]

theorem lintegral_Wp
    (τa : Measure (Ga K))
    (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (GL (Fin 2) (v.adicCompletion K)))
    (hτf : ∀ v, (τf v).IsHaarMeasure)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (τ : Measure (Gp K)) (cτ : ℝ) (hcτ : 0 < cτ)
    (hτprod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable Wa τa →
        (∀ v ∈ S, AEStronglyMeasurable (WS v) (τf v)) →
        (∀ t : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cτ * (∫ x, Wa x ∂τa) * ∏ v ∈ S, ∫ y, WS v y ∂(τf v))
    (y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K) (hy : Measurable y)
    (hWa_top : ∫⁻ h, Wa K y h ∂τa ≠ ⊤) (hWp_top : ∫⁻ g, Wp K y g ∂τ ≠ ⊤) :
    ∫⁻ g, Wp K y g ∂τ =
      ENNReal.ofReal cτ * (∫⁻ h, Wa K y h ∂τa) *
        ∏ v ∈ S₀, τf v (AutomorphicForm.localIntegralSet K v) := by
  haveI := hτf

  set Wc : Gp K → ℂ := fun g => ((Wp K y g).toReal : ℂ) with hWc
  set Wac : Ga K → ℂ := fun h => ((Wa K y h).toReal : ℂ) with hWac
  set WSc : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ :=
    fun v => (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) with hWSc
  have hWac_m : AEStronglyMeasurable Wac τa :=
    (Complex.continuous_ofReal.measurable.comp (measurable_Wa K hy).ennreal_toReal).aestronglyMeasurable
  have hWSc_m : ∀ v ∈ S₀, AEStronglyMeasurable (WSc v) (τf v) := fun v _ =>
    (measurable_const.indicator (AutomorphicForm.isOpen_localIntegralSet K v).measurableSet).aestronglyMeasurable

  have hprod : ∀ t : Gp K, ∏ v ∈ S₀, WSc v (locAt K t v) =
      if ∀ v ∈ S₀, locAt K t v ∈ AutomorphicForm.localIntegralSet K v then 1 else 0 := by
    intro t
    split_ifs with h
    · exact Finset.prod_eq_one fun v hv => by rw [hWSc]; exact Set.indicator_of_mem (h v hv) _
    · obtain ⟨v, hv, hnot⟩ : ∃ v ∈ S₀, locAt K t v ∉ AutomorphicForm.localIntegralSet K v := by
        by_contra hcon
        exact h fun v hv => Classical.by_contradiction fun hn => hcon ⟨v, hv, hn⟩
      exact Finset.prod_eq_zero hv (by rw [hWSc]; exact Set.indicator_of_notMem hnot _)
  have hfac : ∀ t : Gp K,
      (∀ v ∉ S₀, locAt K t v ∈ AutomorphicForm.localIntegralSet K v) →
        Wc t = Wac (arch K t) * ∏ v ∈ S₀, WSc v (locAt K t v) := by
    intro t ht
    rw [hprod]
    by_cases hall : ∀ v ∈ S₀, locAt K t v ∈ AutomorphicForm.localIntegralSet K v
    · have hU : t ∈ Ufin K := fun v => by
        by_cases hv : v ∈ S₀
        · exact hall v hv
        · exact ht v hv
      rw [if_pos hall, mul_one, hWc, hWac]
      simp only [Wp, Set.indicator_of_mem hU, mul_one]
    · have hU : t ∉ Ufin K := fun h => hall fun v _ => h v
      rw [if_neg hall, mul_zero, hWc]
      simp only [Wp, Set.indicator_of_notMem hU, mul_zero, ENNReal.toReal_zero, Complex.ofReal_zero]
  have hzero : ∀ t : Gp K,
      (∃ v ∉ S₀, locAt K t v ∉ AutomorphicForm.localIntegralSet K v) → Wc t = 0 := by
    rintro t ⟨v, -, hv⟩
    have hU : t ∉ Ufin K := fun h => hv (h v)
    rw [hWc]
    simp only [Wp, Set.indicator_of_notMem hU, mul_zero, ENNReal.toReal_zero, Complex.ofReal_zero]
  have h := hτprod S₀ (Finset.Subset.refl _) Wc Wac WSc hWac_m hWSc_m hfac hzero

  have hI1 : ∫ t, Wc t ∂τ = ((∫⁻ g, Wp K y g ∂τ).toReal : ℂ) := by
    simp only [hWc]
    rw [integral_complex_ofReal, integral_toReal (measurable_Wp K hy).aemeasurable
      (ae_of_all _ fun g => (Wp_ne_top K y g).lt_top)]
  have hI2 : ∫ x, Wac x ∂τa = ((∫⁻ h, Wa K y h ∂τa).toReal : ℂ) := by
    simp only [hWac]
    rw [integral_complex_ofReal, integral_toReal (measurable_Wa K hy).aemeasurable
      (ae_of_all _ fun h => (Wa_ne_top K y h).lt_top)]
  have hI3 : ∀ v : HeightOneSpectrum (𝓞 K),
      ∫ z, WSc v z ∂(τf v) = ((τf v (AutomorphicForm.localIntegralSet K v)).toReal : ℂ) := by
    intro v
    simp only [hWSc]
    rw [integral_indicator_const _ (AutomorphicForm.isOpen_localIntegralSet K v).measurableSet,
      measureReal_def, Complex.real_smul, mul_one]
  rw [hI1, hI2] at h
  simp_rw [hI3] at h

  have hR : (∫⁻ g, Wp K y g ∂τ).toReal =
      cτ * (∫⁻ h, Wa K y h ∂τa).toReal * ∏ v ∈ S₀, (τf v (AutomorphicForm.localIntegralSet K v)).toReal := by
    exact_mod_cast h
  have ht_top : ∀ v : HeightOneSpectrum (𝓞 K), τf v (AutomorphicForm.localIntegralSet K v) ≠ ⊤ := fun v =>
    (AutomorphicForm.isCompact_localIntegralSet K v).measure_lt_top.ne
  calc ∫⁻ g, Wp K y g ∂τ = ENNReal.ofReal ((∫⁻ g, Wp K y g ∂τ).toReal) := (ENNReal.ofReal_toReal hWp_top).symm
    _ = ENNReal.ofReal (cτ * (∫⁻ h, Wa K y h ∂τa).toReal *
          ∏ v ∈ S₀, (τf v (AutomorphicForm.localIntegralSet K v)).toReal) := by rw [hR]
    _ = ENNReal.ofReal cτ * (∫⁻ h, Wa K y h ∂τa) * ∏ v ∈ S₀, τf v (AutomorphicForm.localIntegralSet K v) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hcτ.le, ENNReal.ofReal_toReal hWa_top,
        ENNReal.ofReal_prod_of_nonneg (fun v _ => ENNReal.toReal_nonneg)]
      congr 1
      exact Finset.prod_congr rfl fun v _ => ENNReal.ofReal_toReal (ht_top v)

end TauSide

section Main

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

theorem main
    (τa : Measure (Ga K)) (hτa : τa.IsHaarMeasure)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (GL (Fin 2) (v.adicCompletion K)))
    (hτf : ∀ v, (τf v).IsHaarMeasure)
    (n : ℕ) (e : Fin n → Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
      LinearIndependent ℝ e ∧
        Submodule.span ℝ (Set.range e) = ⊤ ∧
        Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
            (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) τa =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
                  Algebra.trace ℝ (InfiniteAdeleRing K) (Matrix.trace (e i * e j))).det|)) •
                Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)| ^ 2)⁻¹))
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (τ : Measure (Gp K)) (hτ : τ.IsHaarMeasure) (cτ : ℝ) (hcτ : 0 < cτ)
    (hτprod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable Wa τa →
        (∀ v ∈ S, AEStronglyMeasurable (WS v) (τf v)) →
        (∀ t : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cτ * (∫ x, Wa x ∂τa) * ∏ v ∈ S, ∫ y, WS v y ∂(τf v))
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure) :
    s ≠ ⊤ ∧
    ∀ (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ENNReal)
      (Ψ : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → ENNReal),
      Measurable w → Measurable Ψ →
      (∀ᵐ g ∂τ, ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1) →
      μ (Ebox K) ^ 3 * ν (Sh K) *
        ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
            Matrix.GeneralLinearGroup.det g) ∂τ =
      ENNReal.ofReal cτ * s * (∏ v ∈ S₀, τf v (AutomorphicForm.localIntegralSet K v)) *
        (2 ^ (4 * NumberField.InfinitePlace.nrComplexPlaces K + NumberField.InfinitePlace.nrRealPlaces K) *
          ENNReal.ofReal ((2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K) *
          ENNReal.ofReal (NumberField.dedekindZeta K 2).re) *
        ∫⁻ c, ∫⁻ δ, Ψ (c, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
          ∂(Measure.pi fun _ : Fin 2 => μ) := by
  haveI := hτa; haveI := hτ; haveI := hμ; haveI := hν

  have hs : s ≠ ⊤ := s_ne_top K τa hτa s _ harch.2.2
  refine ⟨hs, fun w Ψ hw hΨ hw1 => ?_⟩

  set a : ℝ≥0∞ := μ (Ebox K) with ha
  set V : ℝ≥0∞ := ν (Sh K) with hV
  set P : ℝ≥0∞ := (Measure.pi fun _ : Fin 2 => μ) (P1 K) with hP
  set Z : ℝ≥0∞ := ENNReal.ofReal (NumberField.dedekindZeta K 2).re with hZ
  set T : ℝ≥0∞ := ∏ v ∈ S₀, τf v (AutomorphicForm.localIntegralSet K v) with hT
  set X : ℝ≥0∞ := 2 ^ (4 * NumberField.InfinitePlace.nrComplexPlaces K + NumberField.InfinitePlace.nrRealPlaces K) *
    ENNReal.ofReal ((2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K) with hX
  obtain ⟨ha0, hatop⟩ := Ebox_ne_zero_ne_top K μ hμ
  have hVtop : V ≠ ⊤ := (measure_Sh_lt_top K ν).ne
  have hZP : Z * P = a ^ 2 := zeta_mul_measure_P1 K μ hμ
  have hPtop : P ≠ ⊤ := by
    have h : P ≤ a ^ 2 := by
      rw [hP, ha, ← measure_B1 K μ]
      exact measure_mono (P1_subset_B1 K)
    exact ne_top_of_le_ne_top (ENNReal.pow_ne_top hatop) h
  have hXtop : X ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofReal_ne_top

  obtain ⟨c, hc0, hctop, hc⟩ :=
    AutomorphicForm.exists_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_lintegral_ideleNorm_inv_of_ae_lintegral_mul_unipotentGL2_eq_one
      K τ hτ μ hμ ν hν

  obtain ⟨w₀, hw₀m, hw₀⟩ := AutomorphicForm.exists_measurable_forall_lintegral_mul_unipotentGL2_eq_one K μ hμ
  obtain ⟨y, hy, hy1⟩ := AutomorphicForm.exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing K

  have htest := hc (wSharp K y a w₀) (Ψt K) (measurable_wSharp K hy a hw₀m) (measurable_Ψt K)
    (ae_of_all _ (lintegral_wSharp K μ y hy hy1 ha0 hatop hw₀))
  simp_rw [wSharp_mul_Ψt K y a w₀] at htest
  rw [lintegral_const_mul _ (measurable_Wp K hy), I_Ψt K μ ν] at htest

  have hJ : ∫⁻ g, Wp K y g ∂τ = a * (c * (P * V)) := by
    rw [← htest, ← mul_assoc, ENNReal.mul_inv_cancel ha0 hatop, one_mul]
  have hJtop : ∫⁻ g, Wp K y g ∂τ ≠ ⊤ := by
    rw [hJ]
    exact ENNReal.mul_ne_top hatop (ENNReal.mul_ne_top hctop (ENNReal.mul_ne_top hPtop hVtop))

  have hWa : ∫⁻ h, Wa K y h ∂τa = s * X := by
    have hAC := AutomorphicForm.setLIntegral_ofReal_norm_det_eq_mul_two_pow_mul_two_pi_pow_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing
      K τa n e s harch y hy hy1
    change ∫⁻ h in Tset K y,
        ENNReal.ofReal ‖((Matrix.GeneralLinearGroup.det h : (Kinf K)ˣ) : Kinf K)‖ ∂τa = s * X at hAC
    unfold Wa
    rw [lintegral_indicator (measurableSet_Tset K hy)]
    exact hAC
  have hWatop : ∫⁻ h, Wa K y h ∂τa ≠ ⊤ := by
    rw [hWa]; exact ENNReal.mul_ne_top hs hXtop
  have hτside := lintegral_Wp K τa τf hτf S₀ τ cτ hcτ hτprod y hy hWatop hJtop
  rw [hWa] at hτside

  rw [hc w Ψ hw hΨ hw1]
  have key : a ^ 3 * V * c = ENNReal.ofReal cτ * s * T * (X * Z) := by
    calc a ^ 3 * V * c = Z * (a * (c * (P * V))) := by
          rw [show a ^ 3 = a * a ^ 2 by ring, ← hZP]; ring
      _ = Z * (ENNReal.ofReal cτ * (s * X) * T) := by rw [← hJ, hτside]
      _ = ENNReal.ofReal cτ * s * T * (X * Z) := by ring
  calc a ^ 3 * V * (c * ∫⁻ p, ∫⁻ δ, Ψ (p, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
          ∂(Measure.pi fun _ : Fin 2 => μ))
        = (a ^ 3 * V * c) * ∫⁻ p, ∫⁻ δ, Ψ (p, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
          ∂(Measure.pi fun _ : Fin 2 => μ) := by ring
    _ = _ := by rw [key]

end Main

end AutomorphicForm.WeilConstant
p2m_reactivate "P2MW.S_AutomorphicForm_measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm P2MW.S_AutomorphicForm_measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm.WeilConstant"
p2m_reactivate "P2MW.S_AutomorphicForm_measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm P2MW.S_AutomorphicForm_measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one.AutomorphicForm.WeilConstant"

p2m_open "MeasureTheory NumberField NumberField.InfinitePlace.NumberField NumberField.AdelicHaar IsDedekindDomain"

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

    (τa : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hτa : @Measure.IsHaarMeasure (GL (Fin 2) (InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) τa)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (hτf : ∀ v, @Measure.IsHaarMeasure (GL (Fin 2) (v.adicCompletion K)) _ _
      (AutomorphicForm.localGLBorel K v) (τf v))

    (n : ℕ) (e : Fin n → Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
      LinearIndependent ℝ e ∧
        Submodule.span ℝ (Set.range e) = ⊤ ∧
        Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
            (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) τa =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
                  Algebra.trace ℝ (InfiniteAdeleRing K) (Matrix.trace (e i * e j))).det|)) •
                Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)| ^ 2)⁻¹))

    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (τ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hτ : τ.IsHaarMeasure) (cτ : ℝ) (hcτ : 0 < cτ)
    (hτprod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] Wa τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (WS v) (τf v)) →
        (∀ t : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cτ * (∫ x, Wa x ∂τa) * ∏ v ∈ S, ∫ y, WS v y ∂(τf v))

    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure) :
    s ≠ ⊤ ∧
    ∀ (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ENNReal)
      (Ψ : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → ENNReal),
      Measurable w → Measurable Ψ →
      (∀ᵐ g ∂τ, ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1) →
      μ {x | ((∀ w : {w : InfinitePlace K // w.IsReal},
              (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
          x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K} ^ 3 *
        ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} *
        ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
            Matrix.GeneralLinearGroup.det g) ∂τ =
      ENNReal.ofReal cτ * s * (∏ v ∈ S₀, τf v (AutomorphicForm.localIntegralSet K v)) *
        (2 ^ (4 * NumberField.InfinitePlace.nrComplexPlaces K + NumberField.InfinitePlace.nrRealPlaces K) *
          ENNReal.ofReal ((2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K) *
          ENNReal.ofReal (NumberField.dedekindZeta K 2).re) *
        ∫⁻ c, ∫⁻ δ, Ψ (c, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
          ∂(Measure.pi fun _ : Fin 2 => μ) :=
  AutomorphicForm.WeilConstant.main K τa hτa τf hτf n e s harch S₀ τ hτ cτ hcτ hτprod μ hμ ν hν

end S_AutomorphicForm_measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one
end P2MW
export P2MW.S_AutomorphicForm_measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one (solution)
