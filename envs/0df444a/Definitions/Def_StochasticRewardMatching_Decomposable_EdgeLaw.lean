-- Prove2me | Definitions.Def_StochasticRewardMatching_Decomposable_EdgeLaw
-- name    : StochasticRewardMatching_Decomposable_EdgeLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:14:01.208008+00:00
-- url     : https://prove2.me/theorems/a1bc79c6-0881-4ce8-bd95-698fe7a96e6a
-- title:
--   Independent edge outcomes and single-edge resampling
-- statement:
--   The probability of an outcome is the product of its Bernoulli masses over present edges. Edge expectation is the finite weighted sum over all such outcomes. The edge indicator is 1 on success and 0 on failure; querying an absent edge returns false. Resampling a distinguished present edge replaces its bit by false and true with weights 1-p and p, leaving every other bit fixed. This defines the source conditional expectation even for outside configurations of probability zero, without a null-event conditional-expectation convention.
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), §2, PDF/printed p. 9; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Instance

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

def bit {n m : ℕ} (D : Instance n m) (ω : Outcome D) (e : Fin n × Fin m) : Bool :=
  if h : e ∈ D.edges then ω ⟨e, h⟩ else false

def indicator {n m : ℕ} {D : Instance n m} (ω : Outcome D) (e : Edge D) : ℝ :=
  if ω e then 1 else 0

def pathWeight {n m : ℕ} (D : Instance n m) (ω : Outcome D) : ℝ :=
  ∏ e : Edge D, if ω e then D.probability e.val else 1 - D.probability e.val

def edgeAverage {n m : ℕ} (D : Instance n m) (f : Outcome D → ℝ) : ℝ := by
  classical
  exact ∑ ω : Outcome D, pathWeight D ω * f ω

def resample {n m : ℕ} (D : Instance n m) (e : Edge D) (ω : Outcome D)
    (f : Outcome D → ℝ) : ℝ := by
  classical
  exact (1 - D.probability e.val) * f (Function.update ω e false) +
    D.probability e.val * f (Function.update ω e true)

end StochasticRewardMatching.Decomposable


