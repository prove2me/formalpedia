-- Prove2me | Definitions.Def_StochasticRewardMatching_Decomposable_Algorithm
-- name    : StochasticRewardMatching_Decomposable_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:15:24.570001+00:00
-- url     : https://prove2.me/theorems/62b264a0-bc4c-4078-b991-c3d6b1051b6e
-- title:
--   Algorithm 1: generalized perturbed greedy execution
-- statement:
--   Draw one independent uniform real seed for each resource, once for the whole run. At arrival t choose an available neighbor maximizing p_it r_i (1-exp(y_i-1)), breaking ties by the least resource index. If none exists, skip. A success earns r_i and consumes i; a failure leaves it available. The finite recursion records every offer or skip and its realized outcome, and also supports an arbitrary initial subset for the run with one resource removed. The algorithm value averages its realized reward over both the independent edge law and the seed law. Zero scores are handled by the fixed tie rule, and seeds are never refreshed after failures.
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), Algorithm 1, PDF/printed p. 9; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_History
import Definitions.Def_StochasticRewardMatching_Decomposable_Seeds
import Definitions.Def_StochasticRewardMatching_Decomposable_FiniteChoice

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

def score {n m : ℕ} (D : Instance n m) (Y : Seeds n) (t : Fin m) (i : Fin n) : ℝ :=
  D.probability (i, t) * D.reward i * (1 - g (Y i))

def neighbors {n m : ℕ} (D : Instance n m) (S : Finset (Fin n)) (t : Fin m) : Finset (Fin n) :=
  S.filter (fun i => (i, t) ∈ D.edges)

def algorithmChoice {n m : ℕ} (D : Instance n m) (Y : Seeds n)
    (S : Finset (Fin n)) (t : Fin m) : Option (Fin n) :=
  bestOf (score D Y t) ((neighbors D S t).sort (· ≤ ·))

def algorithmRun {n m : ℕ} (D : Instance n m) (Y : Seeds n) (ω : Outcome D)
    (initial : Finset (Fin n)) : ℕ → Finset (Fin n) × History n m
  | 0 => (initial, [])
  | k + 1 =>
      let prev := algorithmRun D Y ω initial k
      if hk : k < m then
        let a : Action n m := (⟨k, hk⟩, algorithmChoice D Y prev.1 ⟨k, hk⟩)
        let b := actionBit D ω a
        (if b then afterSuccess prev.1 a else prev.1, prev.2 ++ [(a,b)])
      else prev

def algorithmHistory {n m : ℕ} (D : Instance n m) (Y : Seeds n) (ω : Outcome D) : History n m :=
  (algorithmRun D Y ω Finset.univ m).2

def algorithmReward {n m : ℕ} (D : Instance n m) (Y : Seeds n) (ω : Outcome D) : ℝ :=
  ((algorithmHistory D Y ω).map (fun z => if z.2 then actionReward D z.1 else 0)).sum

def algorithmValue {n m : ℕ} (D : Instance n m) : ℝ :=
  edgeAverage D (fun ω => seedAverage (fun Y => algorithmReward D Y ω))

end StochasticRewardMatching.Decomposable


