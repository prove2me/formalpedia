-- Prove2me | Definitions.Def_BayesClock_maximalSets
-- name    : BayesClock_maximalSets
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:10.046974+00:00
-- url     : https://prove2.me/theorems/6582016b-e810-4af1-af0f-5c1bd83772ba
-- title:
--   Maximal feasible sets $\mathcal S=(S_1,\dots,S_k)$
-- statement:
--   Given a feasibility constraint $\mathcal F$, the collection $\mathcal S=(S_1,\dots,S_k)$ of **maximal feasible sets** consists of the members of $\mathcal F$ that are not properly contained in another member of $\mathcal F$. The number $k=|\mathcal S|$ is the parameter of every guarantee in the paper.
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, §3, p.6

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- The collection `𝒮 = (S₁, …, S_k)` of maximal feasible sets of `𝓕`: the members of `𝓕` not
properly contained in a member of `𝓕`. Feldman et al., arXiv:2202.09291v1, §3, p.6 ("let
𝒮 = (S1, …, Sk) denote the collection of maximal feasible sets in 𝓕"). The number `k` of the paper
is `(maximalSets 𝓕).card`. -/
def maximalSets {N : Type*} [DecidableEq N] (𝓕 : Finset (Finset N)) : Finset (Finset N) :=
  𝓕.filter (fun F => ¬ ∃ F' ∈ 𝓕, F ⊂ F')

end BayesClock


