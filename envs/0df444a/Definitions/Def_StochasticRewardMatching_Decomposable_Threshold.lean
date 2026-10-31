-- Prove2me | Definitions.Def_StochasticRewardMatching_Decomposable_Threshold
-- name    : StochasticRewardMatching_Decomposable_Threshold
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:17:17.027231+00:00
-- url     : https://prove2.me/theorems/5f3a5905-d65e-40fa-8761-c12154968e41
-- title:
--   The printed critical threshold, including the missing reward factor
-- statement:
--   Remove the distinguished resource i and run the same Algorithm 1 up to just before t, retaining every other seed and edge bit. On the remaining available neighbors at t take max_j p_jt(1-g(y_j)), exactly as printed, without r_j. The critical threshold is 1 for an empty neighbor set, 0 if there is no solution in [0,1] to p_it r_i(1-g(y)) equal to this maximum, and otherwise the largest solution. The root set is closed and bounded, so its nonempty supremum is a root. Choosing the largest root resolves the unspecified zero-coefficient case, including the all-zero case with threshold 1. Removing i makes the result independent of its seed and the distinguished bit. The source error is retained and separately documented as I2.
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), §3.3, unnumbered critical-threshold display, PDF/printed p. 15; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Algorithm

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

def reducedNeighbors {n m : ℕ} (D : Instance n m) (e : Edge D)
    (ω : Outcome D) (Y : Seeds n) : Finset (Fin n) :=
  neighbors D (algorithmRun D Y ω (Finset.univ.erase e.val.1) e.val.2.val).1 e.val.2

def threshold {n m : ℕ} (D : Instance n m) (e : Edge D)
    (ω : Outcome D) (Y : Seeds n) : ℝ := by
  classical
  let N := reducedNeighbors D e ω Y
  let rhs := maxWithZero (N.toList.map (fun j => D.probability (j, e.val.2) * (1 - g (Y j))))
  let roots := {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧
    D.probability e.val * D.reward e.val.1 * (1 - g y) = rhs}
  exact if N = ∅ then 1 else if roots.Nonempty then sSup roots else 0

end StochasticRewardMatching.Decomposable


