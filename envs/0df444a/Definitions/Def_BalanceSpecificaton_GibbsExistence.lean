-- Prove2me | Definitions.Def_BalanceSpecificaton_GibbsExistence
-- name    : BalanceSpecificaton_GibbsExistence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:39:25.782186+00:00
-- url     : https://prove2.me/theorems/8f46b74f-56f0-4a5a-ae3b-0fc85af6fad0
-- title:
--   Gibbs Existence
-- statement:
--   Definitions and structural lemmas for Gibbs Existence, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_extensionPairs
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
section FiniteProbability
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [Nonempty I]
def finitePointMeasure (x : I → Ω) : Measure Ω :=
  (Fintype.card I : ℝ≥0∞)⁻¹ • ∑ i : I, Measure.dirac (x i)
theorem isProbabilityMeasure_finitePointMeasure (x : I → Ω) :
    IsProbabilityMeasure (finitePointMeasure x) := by
  constructor
  simp only [finitePointMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
    (by simp only [ENNReal.natCast_ne_top, ne_eq, not_false_eq_true])
def finitePointProbability (x : I → Ω) : ProbabilityMeasure Ω :=
  ⟨finitePointMeasure x, isProbabilityMeasure_finitePointMeasure x⟩
end FiniteProbability
section FiniteOrbitProbability
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [Nonempty I]
def finiteOrbitProbability (f : Ω → Ω) (x : I → Ω) (n : ℕ) : ProbabilityMeasure Ω :=
  finitePointProbability fun p : I × Fin (n + 1) => f^[p.2.val] (x p.1)
end FiniteOrbitProbability
section OrbitCluster
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [T2Space Ω]
    [HasOuterApproxClosed Ω]
    {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, Nonempty (I n)]
end OrbitCluster
section WordProbabilities
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
end WordProbabilities
end BalanceSpecification


