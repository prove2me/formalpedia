-- Prove2me | Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
-- name    : LeanPool_PebblingLean_UpperBoundProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:50:42.278835+00:00
-- url     : https://prove2.me/theorems/deb6f7f4-1660-47ae-a37a-a782d43b8093
-- title:
--   Upper Bound Probability
-- statement:
--   Definitions and structural lemmas for Upper Bound Probability, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace Hypercube
open Pebbling
open FiniteProbability
abbrev CenterSample (n N : ℕ) := Fin N → HypercubeVertex n
def CenterSample.toList {n N : ℕ} (sample : CenterSample n N) :
    List (HypercubeVertex n) :=
  List.ofFn sample
def sampleTotalContribution {n N : ℕ} (rIn rOut : ℕ)
    (target : HypercubeVertex n) (sample : CenterSample n N) : ℕ :=
  ∑ j : Fin N, annulusContribution rIn rOut target (sample j)
noncomputable def oneCenterContributionExpectation {n : ℕ} (rIn rOut : ℕ)
    (target : HypercubeVertex n) : ℚ :=
  uniformExpectation fun center : HypercubeVertex n =>
    annulusContribution rIn rOut target center
noncomputable def oneCenterContributionExpectationReal {n : ℕ} (rIn rOut : ℕ)
    (target : HypercubeVertex n) : ℝ :=
  uniformExpectationReal fun center : HypercubeVertex n =>
    (annulusContribution rIn rOut target center : ℝ)
noncomputable def oneCenterContributionSecondMoment {n : ℕ} (rIn rOut : ℕ)
    (target : HypercubeVertex n) : ℚ :=
  uniformExpectation fun center : HypercubeVertex n =>
    (annulusContribution rIn rOut target center) ^ 2
def annulusMeanNumerator (n rIn rOut : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1),
    Nat.choose n i *
      if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0
noncomputable def annulusMean (n rIn rOut : ℕ) : ℚ :=
  (annulusMeanNumerator n rIn rOut : ℚ) / (2 ^ n : ℚ)
noncomputable def binomialWindowProbThird (n rIn rOut : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    if rIn ≤ i ∧ i ≤ rOut then
      (Nat.choose n i : ℝ) * (((1 : ℝ) / 3) ^ i) * (((2 : ℝ) / 3) ^ (n - i))
    else
      0
noncomputable def binomialMassThird (n i : ℕ) : ℝ :=
  (Nat.choose n i : ℝ) * (((1 : ℝ) / 3) ^ i) * (((2 : ℝ) / 3) ^ (n - i))
noncomputable def binomialLeftTailProbThird (n rIn : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    if i < rIn then binomialMassThird n i else 0
noncomputable def binomialRightTailProbThird (n rOut : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    if rOut < i then binomialMassThird n i else 0
noncomputable def sampleContributionExpectation {n N : ℕ} (rIn rOut : ℕ)
    (target : HypercubeVertex n) : ℚ :=
  uniformExpectation fun sample : CenterSample n N =>
    sampleTotalContribution rIn rOut target sample
noncomputable def sampleContributionSecondMomentProxy {n N : ℕ} (rIn rOut : ℕ)
    (target : HypercubeVertex n) : ℚ :=
  (N : ℚ) * oneCenterContributionSecondMoment rIn rOut target
def sampleTargetFails {n N : ℕ} (rIn rOut T : ℕ)
    (target : HypercubeVertex n) (sample : CenterSample n N) : Prop :=
  sampleTotalContribution rIn rOut target sample < T
instance instDecidableSampleTargetFails {n N rIn rOut T : ℕ}
    (target : HypercubeVertex n) (sample : CenterSample n N) :
    Decidable (sampleTargetFails rIn rOut T target sample) := by
  unfold sampleTargetFails
  infer_instance
instance instDecidablePredSampleTargetFails {n N rIn rOut T : ℕ}
    (target : HypercubeVertex n) :
    DecidablePred (sampleTargetFails (n := n) (N := N) rIn rOut T target) :=
  fun sample => instDecidableSampleTargetFails target sample
def sampleFailsSomeTarget {n N : ℕ} (rIn rOut T : ℕ)
    (sample : CenterSample n N) : Prop :=
  ∃ target : HypercubeVertex n, sampleTargetFails rIn rOut T target sample
instance instDecidableSampleFailsSomeTarget {n N rIn rOut T : ℕ}
    (sample : CenterSample n N) :
    Decidable (sampleFailsSomeTarget rIn rOut T sample) := by
  classical
  unfold sampleFailsSomeTarget
  infer_instance
instance instDecidablePredSampleFailsSomeTarget {n N rIn rOut T : ℕ} :
    DecidablePred (sampleFailsSomeTarget (n := n) (N := N) rIn rOut T) :=
  fun sample => instDecidableSampleFailsSomeTarget sample
noncomputable def targetFailureProbability {n N : ℕ} (rIn rOut T : ℕ)
    (target : HypercubeVertex n) : ℚ :=
  uniformProbability fun sample : CenterSample n N =>
    sampleTargetFails rIn rOut T target sample
noncomputable def targetFailureProbabilityReal {n N : ℕ} (rIn rOut T : ℕ)
    (target : HypercubeVertex n) : ℝ :=
  uniformProbabilityReal fun sample : CenterSample n N =>
    sampleTargetFails rIn rOut T target sample
noncomputable def targetLowerTailExponentialMoment {n N : ℕ}
    (rIn rOut T : ℕ) (target : HypercubeVertex n) (lam : ℝ) : ℝ :=
  uniformExpectationReal fun sample : CenterSample n N =>
    Real.exp (lam * ((T : ℝ) - (sampleTotalContribution rIn rOut target sample : ℝ)))
noncomputable def oneCenterNegativeExponentialMoment {n : ℕ}
    (rIn rOut : ℕ) (target : HypercubeVertex n) (lam : ℝ) : ℝ :=
  uniformExpectationReal fun center : HypercubeVertex n =>
    Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))
def OneCenterExponentialMomentBound (n N rIn rOut T : ℕ) (lam eps : ℝ) : Prop :=
  0 < lam ∧
    Real.exp (lam * (T : ℝ)) *
      (oneCenterNegativeExponentialMoment rIn rOut (fun _ : Fin n => false) lam) ^ N ≤ eps
def OneCenterDistanceSumExponentialMomentBound
    (n N rIn rOut T : ℕ) (lam eps : ℝ) : Prop :=
  0 < lam ∧
    Real.exp (lam * (T : ℝ)) *
      (((∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          Real.exp
            (-(lam *
              ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)))) /
        (2 ^ n : ℝ)) ^ N) ≤ eps
noncomputable def globalFailureProbability {n N : ℕ} (rIn rOut T : ℕ) : ℚ :=
  uniformProbability fun sample : CenterSample n N =>
    sampleFailsSomeTarget rIn rOut T sample
def ChernoffMeanLowerBound (n N rIn rOut T : ℕ) : Prop :=
  ∀ target : HypercubeVertex n,
    (T : ℚ) ≤ sampleContributionExpectation (n := n) (N := N) rIn rOut target
def BernsteinTargetFailureBound (n N rIn rOut T : ℕ) (eps : ℚ) : Prop :=
  ∀ target : HypercubeVertex n,
    targetFailureProbability (n := n) (N := N) rIn rOut T target ≤ eps
def ChernoffExponentialMomentBound (n N rIn rOut T : ℕ) (eps : ℝ) : Prop :=
  ∀ target : HypercubeVertex n,
    ∃ lam : ℝ,
      0 < lam ∧
        targetLowerTailExponentialMoment (n := n) (N := N) rIn rOut T target lam ≤ eps
noncomputable def bernsteinExponent (variance scale gap : ℝ) : ℝ :=
  gap ^ 2 / (2 * (variance + scale * gap / 3))
def BernsteinExponentialMomentBound (n N rIn rOut T : ℕ)
    (variance scale gap : ℝ) : Prop :=
  ChernoffExponentialMomentBound n N rIn rOut T
    (Real.exp (-(bernsteinExponent variance scale gap)))
end Hypercube
end PebblingLean


