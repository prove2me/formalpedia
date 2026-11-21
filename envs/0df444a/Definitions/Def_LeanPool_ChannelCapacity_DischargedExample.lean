-- Prove2me | Definitions.Def_LeanPool_ChannelCapacity_DischargedExample
-- name    : LeanPool_ChannelCapacity_DischargedExample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:49:02.000327+00:00
-- url     : https://prove2.me/theorems/a4201b6d-5426-4799-9e43-9badf0e31d7c
-- title:
--   Discharged Example
-- statement:
--   Definitions and structural lemmas for Discharged Example, from Adam Benenson and LeanPool contributors's pinned Uniqueness of capacity-achieving priors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/DischargedExample.lean

module
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Theorems.Thm_ChannelCapacity_Kernel_injectivePriorPushforward_of_rowMatrixFullRank
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_continuous_mutualInformation_of_finite
public import Theorems.Thm_ChannelCapacity_exists_unique_capacity_achieving_prior_discharged
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_ChannelCapacity_toMeasure_eq_count_withDensity
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_dirac
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_id
attribute [local simp] ChannelCapacity.independentJointLaw_toMeasure
attribute [local simp] ChannelCapacity.jointLaw_toMeasure
attribute [local simp] ChannelCapacity.outputPrior_toMeasure
attribute [local simp] ProbabilityMeasure.convexCombination_toMeasure


set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal NNReal
namespace ChannelCapacity.DischargedExample
lemma threeQuarter_add_oneQuarter :
    (3 / 4 : ℝ≥0∞) + 1 / 4 = 1 := by
  have h : ((3 / 4 : ℝ≥0) + 1 / 4 : ℝ≥0) = 1 := by
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)
lemma oneQuarter_add_threeQuarter :
    (1 / 4 : ℝ≥0∞) + 3 / 4 = 1 := by
  simpa [add_comm] using threeQuarter_add_oneQuarter
noncomputable def twoByTwoRowPMF : Fin 2 → PMF (Fin 2)
  | 0 => PMF.ofFintype (fun
      | 0 => (3 / 4 : ℝ≥0∞)
      | _ => (1 / 4 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_two] using threeQuarter_add_oneQuarter)
  | _ => PMF.ofFintype (fun
      | 0 => (1 / 4 : ℝ≥0∞)
      | _ => (3 / 4 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_two] using oneQuarter_add_threeQuarter)
noncomputable def twoByTwoRows (i : Fin 2) : ProbabilityMeasure (Fin 2) :=
  ⟨(twoByTwoRowPMF i).toMeasure, by infer_instance⟩
@[simp]
lemma twoByTwoRows_apply_singleton (i j : Fin 2) :
    (twoByTwoRows i).toMeasure {j} = twoByTwoRowPMF i j := by
  simp [twoByTwoRows]
noncomputable def twoByTwoKernel : Kernel (Fin 2) (Fin 2) :=
  Kernel.ofFunOfCountable fun i => (twoByTwoRows i).toMeasure
@[simp]
lemma twoByTwoKernel_apply (i : Fin 2) :
    twoByTwoKernel i = (twoByTwoRows i).toMeasure := by
  rfl
lemma twoByTwoKernel_apply_singleton (i j : Fin 2) :
    twoByTwoKernel i {j} = twoByTwoRowPMF i j := by
  simp [twoByTwoKernel_apply, twoByTwoRows]
noncomputable instance twoByTwoKernel_isMarkov : IsMarkovKernel twoByTwoKernel := by
  constructor
  intro i
  change IsProbabilityMeasure ((twoByTwoRowPMF i).toMeasure)
  infer_instance
noncomputable def twoByTwoDensity (i j : Fin 2) : NNReal :=
  if i = j then 3 / 4 else 1 / 4
@[simp]
lemma twoByTwoDensity_apply (i j : Fin 2) :
    (twoByTwoDensity i j : ℝ≥0∞) = twoByTwoRowPMF i j := by
  fin_cases i <;> fin_cases j <;> simp [twoByTwoDensity, twoByTwoRowPMF]
theorem twoByTwo_rowMatrixFullRank : Kernel.RowMatrixFullRank twoByTwoKernel := by
  intro w v hEq
  funext a
  fin_cases a
  · have h0 := congrFun hEq 0
    have h1 := congrFun hEq 1
    norm_num [Fin.sum_univ_two, twoByTwoKernel_apply_singleton, twoByTwoRowPMF] at h0 h1 ⊢
    nlinarith
  · have h0 := congrFun hEq 0
    have h1 := congrFun hEq 1
    norm_num [Fin.sum_univ_two, twoByTwoKernel_apply_singleton, twoByTwoRowPMF] at h0 h1 ⊢
    nlinarith
theorem twoByTwo_injectivePriorPushforward :
    Kernel.InjectivePriorPushforward twoByTwoKernel :=
  Kernel.injectivePriorPushforward_of_rowMatrixFullRank twoByTwoKernel twoByTwo_rowMatrixFullRank
noncomputable def twoByTwoContinuousPositiveDensity :
    Kernel.ContinuousPositiveDensity twoByTwoKernel Measure.count := by
  refine
    { density := twoByTwoDensity
      continuous_density := by
        fun_prop
      eq_withDensity := ?_
      density_pos := ?_
      mutualInformation_usc := ?_ }
  · intro i
    have hcount := ChannelCapacity.toMeasure_eq_count_withDensity (μ := twoByTwoRows i)
    simpa [twoByTwoRows, twoByTwoDensity_apply] using hcount
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [twoByTwoDensity]
  · exact (continuous_mutualInformation_of_finite (k := twoByTwoKernel)).upperSemicontinuous
example :
    ∃! p : ProbabilityMeasure (Fin 2),
      mutualInformation p twoByTwoKernel = channelCapacity twoByTwoKernel :=
  exists_unique_capacity_achieving_prior_discharged
    (k := twoByTwoKernel)
    (ν := Measure.count)
    twoByTwoContinuousPositiveDensity
    twoByTwo_injectivePriorPushforward
end ChannelCapacity.DischargedExample


