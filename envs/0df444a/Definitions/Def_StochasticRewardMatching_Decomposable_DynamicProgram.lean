-- Prove2me | Definitions.Def_StochasticRewardMatching_Decomposable_DynamicProgram
-- name    : StochasticRewardMatching_Decomposable_DynamicProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:17:36.004331+00:00
-- url     : https://prove2.me/theorems/878fd9e1-485c-4a4f-ae0a-e2d0804bae3e
-- title:
--   Finite benchmark dynamic program and its deterministic policy
-- statement:
--   At state (remaining resources S, remaining arrivals U) and remaining action budget k, the dynamic program has value zero at k=0. At k+1 it takes the maximum of stop value zero and the expected immediate reward plus continuation over all legal actions. Each action deletes its arrival, and a successful offer also deletes its resource. The ordered version restricts actions to the earliest remaining arrival, including discarding it; the fully offline version maximizes over every remaining arrival. The deterministic dpPolicy recomputes S and U from observed history and chooses an action maximizing the continuation with fuel |U|-1. Initially the fuel is m. This is a concrete finite recursion, without a field assuming that it dominates any policy.
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), Lemma 1, PDF/printed p. 9; Appendix A.2, PDF/printed p. 36; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Benchmarks
import Definitions.Def_StochasticRewardMatching_Decomposable_FiniteChoice

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

def dp {n m : ℕ} (D : Instance n m) (ordered : Bool) :
    ℕ → Finset (Fin n) → Finset (Fin m) → ℝ
  | 0, _, _ => 0
  | k + 1, S, U => maxWithZero ((legalActions D ordered S U).toList.map fun a =>
      actionProbability D a * (actionReward D a + dp D ordered k (afterSuccess S a) (U.erase a.1)) +
      (1 - actionProbability D a) * dp D ordered k S (U.erase a.1))

def dpPolicy {n m : ℕ} (D : Instance n m) (ordered : Bool) : DetPolicy n m :=
  fun h =>
    let S := remainingResources h
    let U := remainingArrivals h
    bestOf (fun a =>
      actionProbability D a * (actionReward D a + dp D ordered (U.card - 1) (afterSuccess S a) (U.erase a.1)) +
      (1 - actionProbability D a) * dp D ordered (U.card - 1) S (U.erase a.1))
      (legalActions D ordered S U).toList

end StochasticRewardMatching.Decomposable


