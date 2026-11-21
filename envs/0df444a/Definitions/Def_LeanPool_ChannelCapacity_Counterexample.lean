-- Prove2me | Definitions.Def_LeanPool_ChannelCapacity_Counterexample
-- name    : LeanPool_ChannelCapacity_Counterexample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:44:14.94032+00:00
-- url     : https://prove2.me/theorems/380c18d4-9808-42d8-8283-064a3c163b3f
-- title:
--   Counterexample
-- statement:
--   Definitions and structural lemmas for Counterexample, from Adam Benenson and LeanPool contributors's pinned Uniqueness of capacity-achieving priors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Counterexample.lean

module
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Theorems.Thm_ChannelCapacity_Kernel_id_injectivePriorPushforward
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_convexCombination
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_ProbabilityMeasure_convexCombination_apply
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
namespace ChannelCapacity.Counterexample
noncomputable def asProbabilityMeasure {α : Type*} [MeasurableSpace α] (p : PMF α) :
    ProbabilityMeasure α :=
  ⟨p.toMeasure, by infer_instance⟩
noncomputable def uniformTriple {α : Type*} [MeasurableSpace α] (a b c : α) :
    ProbabilityMeasure α :=
  ProbabilityMeasure.convexCombination
    (MeasureTheory.diracProba a)
    (ProbabilityMeasure.convexCombination
      (MeasureTheory.diracProba b)
      (MeasureTheory.diracProba c)
      (1 / 2)
      (by
        have h : (1 : ℝ) / 2 ≤ 1 := by norm_num
        exact_mod_cast h))
    (1 / 3)
    (by
      have h : (1 : ℝ) / 3 ≤ 1 := by norm_num
      exact_mod_cast h)
lemma permutationWeightSum :
    (1 / 2 : ℝ≥0∞) + 1 / 3 + 1 / 6 = 1 := by
  have h : ((1 / 2 : ℝ≥0) + 1 / 3 + 1 / 6 : ℝ≥0) = 1 := by
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)
lemma prior₁_case0 :
    (1 / 3 : ℝ≥0∞) * (1 / 2) + (1 - 1 / 3) * ((1 / 2) * (1 / 6) + (1 / 2) * (1 / 3)) =
      1 / 3 := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 2) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 6) + (1 / 2) * (1 / 3)) : ℝ≥0) = 1 / 3 := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)
lemma prior₁_case1 :
    (1 / 3 : ℝ≥0∞) * (1 / 3) + (1 - 1 / 3) * ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 6)) =
      (1 - 1 / 3) * (1 / 2) := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 3) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 6)) : ℝ≥0) = ((1 : ℝ≥0) - 1 / 3) * (1 / 2) := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)
lemma prior₁_case2 :
    (1 / 3 : ℝ≥0∞) * (1 / 6) + (1 - 1 / 3) * ((1 / 2) * (1 / 3) + (1 / 2) * (1 / 2)) =
      (1 - 1 / 3) * (1 / 2) := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 6) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 3) + (1 / 2) * (1 / 2)) : ℝ≥0) = ((1 : ℝ≥0) - 1 / 3) * (1 / 2) := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)
lemma prior₂_case1 :
    (1 / 3 : ℝ≥0∞) * (1 / 6) + (1 - 1 / 3) * ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 3)) =
      (1 - 1 / 3) * (1 / 2) := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 6) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 3)) : ℝ≥0) = ((1 : ℝ≥0) - 1 / 3) * (1 / 2) := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)
lemma prior₂_case2 :
    (1 / 3 : ℝ≥0∞) * (1 / 3) + (1 - 1 / 3) * ((1 / 2) * (1 / 6) + (1 / 2) * (1 / 2)) =
      (1 - 1 / 3) * (1 / 2) := by
  have h : ((1 / 3 : ℝ≥0) * (1 / 3) + ((1 : ℝ≥0) - 1 / 3) *
      ((1 / 2) * (1 / 6) + (1 / 2) * (1 / 2)) : ℝ≥0) = ((1 : ℝ≥0) - 1 / 3) * (1 / 2) := by
    apply NNReal.coe_injective
    simp
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)
noncomputable def rowPMF : Fin 6 → PMF (Fin 3)
  | 0 => PMF.ofFintype (fun
      | 0 => (1 / 2 : ℝ≥0∞)
      | 1 => (1 / 3 : ℝ≥0∞)
      | _ => (1 / 6 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_assoc] using permutationWeightSum)
  | 1 => PMF.ofFintype (fun
      | 0 => (1 / 2 : ℝ≥0∞)
      | 1 => (1 / 6 : ℝ≥0∞)
      | _ => (1 / 3 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
  | 2 => PMF.ofFintype (fun
      | 0 => (1 / 3 : ℝ≥0∞)
      | 1 => (1 / 2 : ℝ≥0∞)
      | _ => (1 / 6 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
  | 3 => PMF.ofFintype (fun
      | 0 => (1 / 6 : ℝ≥0∞)
      | 1 => (1 / 2 : ℝ≥0∞)
      | _ => (1 / 3 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
  | 4 => PMF.ofFintype (fun
      | 0 => (1 / 3 : ℝ≥0∞)
      | 1 => (1 / 6 : ℝ≥0∞)
      | _ => (1 / 2 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
  | _ => PMF.ofFintype (fun
      | 0 => (1 / 6 : ℝ≥0∞)
      | 1 => (1 / 3 : ℝ≥0∞)
      | _ => (1 / 2 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using permutationWeightSum)
noncomputable def permutationRows : Fin 6 → ProbabilityMeasure (Fin 3) :=
  fun i => asProbabilityMeasure (rowPMF i)
@[simp]
lemma permutationRows_apply_singleton (i : Fin 6) (y : Fin 3) :
    (permutationRows i).toMeasure {y} = rowPMF i y := by
  simp [permutationRows, asProbabilityMeasure]
noncomputable def permutationKernel : Kernel (Fin 6) (Fin 3) :=
  Kernel.ofFunOfCountable fun i => (permutationRows i).toMeasure
@[simp]
lemma permutationKernel_apply (i : Fin 6) :
    permutationKernel i = (rowPMF i).toMeasure := by
  rfl
noncomputable instance permutationKernel_isMarkov :
    IsMarkovKernel permutationKernel := by
  constructor
  intro i
  change IsProbabilityMeasure ((rowPMF i).toMeasure)
  infer_instance
lemma priorPushforward_diracProba (i : Fin 6) :
    ChannelCapacity.Kernel.priorPushforward permutationKernel (MeasureTheory.diracProba i) =
      permutationRows i :=
  ChannelCapacity.Kernel.priorPushforward_dirac permutationKernel i
noncomputable def prior₁ : ProbabilityMeasure (Fin 6) :=
  uniformTriple 0 3 4
noncomputable def prior₂ : ProbabilityMeasure (Fin 6) :=
  uniformTriple 1 2 5
noncomputable def uniformOutput : ProbabilityMeasure (Fin 3) :=
  uniformTriple 0 1 2
def rowCode : Fin 6 → Fin 3 → Rat
  | 0, 0 => 1 / 2
  | 0, 1 => 1 / 3
  | 0, _ => 1 / 6
  | 1, 0 => 1 / 2
  | 1, 1 => 1 / 6
  | 1, _ => 1 / 3
  | 2, 0 => 1 / 3
  | 2, 1 => 1 / 2
  | 2, _ => 1 / 6
  | 3, 0 => 1 / 6
  | 3, 1 => 1 / 2
  | 3, _ => 1 / 3
  | 4, 0 => 1 / 3
  | 4, 1 => 1 / 6
  | 4, _ => 1 / 2
  | _, 0 => 1 / 6
  | _, 1 => 1 / 3
  | _, _ => 1 / 2
def prior₁Code : Fin 6 → Rat
  | 0 => 1 / 3
  | 3 => 1 / 3
  | 4 => 1 / 3
  | _ => 0
def prior₂Code : Fin 6 → Rat
  | 1 => 1 / 3
  | 2 => 1 / 3
  | 5 => 1 / 3
  | _ => 0
def outputCode (w : Fin 6 → Rat) : Fin 3 → Rat :=
  fun y => ∑ x, w x * rowCode x y
lemma prior_ne : prior₁ ≠ prior₂ := by
  intro h
  have h0 := congrArg (fun p : ProbabilityMeasure (Fin 6) => p.toMeasure {0}) h
  simp [prior₁, prior₂, uniformTriple, ProbabilityMeasure.convexCombination_toMeasure,
    Measure.add_apply, Measure.smul_apply] at h0
lemma pushforward_prior₁ :
    ChannelCapacity.Kernel.priorPushforward permutationKernel prior₁ = uniformOutput := by
  change ChannelCapacity.Kernel.priorPushforward permutationKernel (uniformTriple 0 3 4) =
    uniformOutput
  rw [uniformTriple, ChannelCapacity.Kernel.priorPushforward_convexCombination,
    priorPushforward_diracProba,
    ChannelCapacity.Kernel.priorPushforward_convexCombination,
    priorPushforward_diracProba,
    priorPushforward_diracProba]
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro y
  have hs : MeasurableSet ({y} : Set (Fin 3)) := MeasurableSet.singleton y
  rw [uniformOutput, uniformTriple]
  repeat rw [ProbabilityMeasure.convexCombination_apply _ _ _ _ hs]
  fin_cases y
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₁_case0
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₁_case1
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₁_case2
lemma pushforward_prior₂ :
    ChannelCapacity.Kernel.priorPushforward permutationKernel prior₂ = uniformOutput := by
  change ChannelCapacity.Kernel.priorPushforward permutationKernel (uniformTriple 1 2 5) =
    uniformOutput
  rw [uniformTriple, ChannelCapacity.Kernel.priorPushforward_convexCombination,
    priorPushforward_diracProba,
    ChannelCapacity.Kernel.priorPushforward_convexCombination,
    priorPushforward_diracProba,
    priorPushforward_diracProba]
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro y
  have hs : MeasurableSet ({y} : Set (Fin 3)) := MeasurableSet.singleton y
  rw [uniformOutput, uniformTriple]
  repeat rw [ProbabilityMeasure.convexCombination_apply _ _ _ _ hs]
  fin_cases y
  · simp [rowPMF, add_comm]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₁_case0
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₂_case1
  · simp [rowPMF]
    simpa [one_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      prior₂_case2
theorem permutationKernel_not_injectivePriorPushforward :
    ¬ ChannelCapacity.Kernel.InjectivePriorPushforward permutationKernel := by
  intro h
  exact prior_ne (h (pushforward_prior₁.trans pushforward_prior₂.symm))
lemma rowPMF_injective : Function.Injective rowPMF := by
  intro i j hij
  have h0 := congrArg (fun p : PMF (Fin 3) => p 0) hij
  have h1 := congrArg (fun p : PMF (Fin 3) => p 1) hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exfalso; simp [rowPMF, PMF.ofFintype_apply] at h0 h1)
example : ChannelCapacity.Kernel.RowSeparating permutationKernel := by
  intro i j hij hEq
  have hmeas : (rowPMF i).toMeasure = (rowPMF j).toMeasure := by
    simpa using hEq
  exact hij (rowPMF_injective (PMF.toMeasure_injective hmeas))
example :
    ¬ ChannelCapacity.Kernel.InjectivePriorPushforward permutationKernel :=
  permutationKernel_not_injectivePriorPushforward
example :
    ChannelCapacity.Kernel.priorPushforward permutationKernel prior₁ =
      ChannelCapacity.Kernel.priorPushforward permutationKernel prior₂ := by
  rw [pushforward_prior₁, pushforward_prior₂]
namespace Toy
noncomputable def identityKernel : Kernel (Fin 3) (Fin 3) := Kernel.id
noncomputable instance : IsMarkovKernel identityKernel := by
  dsimp [identityKernel]
  infer_instance
example : ChannelCapacity.Kernel.InjectivePriorPushforward identityKernel :=
  ChannelCapacity.Kernel.id_injectivePriorPushforward
end Toy
end ChannelCapacity.Counterexample


