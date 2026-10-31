-- Prove2me | Definitions.Def_StochasticRewardMatching_Decomposable_Benchmarks
-- name    : StochasticRewardMatching_Decomposable_Benchmarks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:15:32.175824+00:00
-- url     : https://prove2.me/theorems/f05d3c79-ebdb-483f-8ea9-6178b1e28087
-- title:
--   Adaptive randomized offline benchmark values
-- statement:
--   A deterministic policy is the published bare history-to-next-action-or-stop policy; its execution uses the published runPolicy recursion. Illegal proposals are converted to stop. A randomized policy supplies an arbitrary probability distribution on next action or stop at each observed history. Its expected continuation is computed recursively by averaging the action distribution and then the independent Bernoulli outcome; no unused edge outcome is revealed. At most m actions are processed. A benchmark is the supremum of these expected rewards, in ordered mode for clairvoyant and unrestricted arrival-order mode for fully offline. These are behavioral policies with full observed-history recall: arbitrary internal randomness induces such conditional action distributions on each finite instance. The value set contains the always-stop value zero and is bounded above by the sum of resource rewards. Thus neither supremum uses an empty or unbounded default. Deterministic optimality is not part of this definition.
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), §§1–2 and Lemma 1, PDF/printed pp. 3, 8–9; Appendix A.2, p. 36; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_History
import Definitions.Def_OfflineStochMatching_UnitPatience_Policy
import Definitions.Def_OfflineStochMatching_UnitPatience_runPolicy

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

abbrev DetPolicy (n m : ℕ) := OfflineStochMatching.UnitPatience.Policy (Action n m)
abbrev RandPolicy (n m : ℕ) := History n m → PMF (Option (Action n m))

def legalize {n m : ℕ} (D : Instance n m) (ordered : Bool) (π : DetPolicy n m)
    (h : History n m) : Option (Action n m) := by
  classical
  exact match π h with
  | none => none
  | some a => if a ∈ legalActions D ordered (remainingResources h) (remainingArrivals h)
      then some a else none

def deterministicValue {n m : ℕ} (D : Instance n m) (ordered : Bool)
    (π : DetPolicy n m) : ℝ :=
  edgeAverage D fun ω =>
    ((OfflineStochMatching.UnitPatience.runPolicy (legalize D ordered π)
      (actionBit D ω) m).map (fun z => if z.2 then actionReward D z.1 else 0)).sum

def randomizedContinuation {n m : ℕ} (D : Instance n m) (ordered : Bool)
    (π : RandPolicy n m) : ℕ → History n m → ℝ
  | 0, _ => 0
  | k + 1, h => by
    classical
    exact ∑ a : Option (Action n m), (π h a).toReal *
      match a with
      | none => 0
      | some a => if a ∈ legalActions D ordered (remainingResources h) (remainingArrivals h) then
          actionProbability D a * (actionReward D a + randomizedContinuation D ordered π k (h ++ [(a, true)])) +
          (1 - actionProbability D a) * randomizedContinuation D ordered π k (h ++ [(a, false)])
        else 0

def randomizedValue {n m : ℕ} (D : Instance n m) (ordered : Bool)
    (π : RandPolicy n m) : ℝ := randomizedContinuation D ordered π m []

def benchmark {n m : ℕ} (D : Instance n m) (ordered : Bool) : ℝ :=
  sSup (Set.range (randomizedValue D ordered))

end StochasticRewardMatching.Decomposable


