-- Prove2me | Definitions.Def_StochasticRewardMatching_Decomposable_FiniteChoice
-- name    : StochasticRewardMatching_Decomposable_FiniteChoice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:13:25.462985+00:00
-- url     : https://prove2.me/theorems/756f52b4-84df-4875-9a5e-1359875775a6
-- title:
--   Finite maximization with explicit empty and tie conventions
-- statement:
--   bestOf selects a maximizer from a finite list, preferring the first list entry on ties and returning none for an empty list. maxWithZero takes the maximum of the list together with zero. These finite recursion helpers supply Algorithm 1 and the benchmark dynamic program; they assert no optimality theorem. Algorithm 1 passes a list sorted by increasing resource index.
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), Algorithm 1, PDF/printed p. 9; Appendix A.2, PDF/printed p. 36; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

def bestOf {α : Type} (score : α → ℝ) : List α → Option α
  | [] => none
  | a :: rest => match bestOf score rest with
    | none => some a
    | some b => if score b ≤ score a then some a else some b

def maxWithZero (xs : List ℝ) : ℝ := xs.foldr max 0

end StochasticRewardMatching.Decomposable


