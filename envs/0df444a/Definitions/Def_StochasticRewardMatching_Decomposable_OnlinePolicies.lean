-- Prove2me | Definitions.Def_StochasticRewardMatching_Decomposable_OnlinePolicies
-- name    : StochasticRewardMatching_Decomposable_OnlinePolicies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:15:47.449822+00:00
-- url     : https://prove2.me/theorems/4fe648d9-977e-40c1-b633-a01b21f516dc
-- title:
--   General randomized online algorithms and expected rewards
-- statement:
--   The revealed input at time t consists of the incident edge sets and probabilities at arrivals up to t; all later rows are hidden. An online rule receives the known resource rewards, current time, that revealed input, and the history of its own actions and observed outcomes, and chooses any probability distribution over resources or skip. It has no access to future rows, endpoint factors, or unused outcomes. Invalid proposals are treated as skips. The expectation is computed by a finite recursion over those action distributions and Bernoulli outcomes, consuming the arrival in both success and failure branches. OnlineFamily supplies such a rule for every finite size. Behavioral policies encompass arbitrary private randomness by conditioning its action distribution on the complete observable history; no finite seed or priority restriction is imposed. The dimensions are known, which also permits algorithms that ignore the horizon.
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), §§1–2 and Theorem 1, PDF/printed pp. 2–5, 8–9; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_History

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

abbrev Revealed (n m : ℕ) := Fin m → Option (Fin n → Option ℝ)

def reveal {n m : ℕ} (D : Instance n m) (t : Fin m) : Revealed n m := by
  classical
  exact fun s => if s ≤ t then some (fun i =>
    if (i, s) ∈ D.edges then some (D.probability (i, s)) else none) else none

abbrev OnlineRule (n m : ℕ) :=
  (Fin n → ℝ) → Fin m → Revealed n m → History n m → PMF (Option (Fin n))
abbrev OnlineFamily := ∀ n m : ℕ, OnlineRule n m

def onlineContinuation {n m : ℕ} (D : Instance n m) (A : OnlineRule n m) :
    ℕ → ℕ → History n m → ℝ
  | 0, _, _ => 0
  | k + 1, t, h => by
    classical
    exact if ht : t < m then
      let τ : Fin m := ⟨t, ht⟩
      ∑ a : Option (Fin n), (A D.reward τ (reveal D τ) h a).toReal *
        match a with
        | none => onlineContinuation D A k (t+1) (h ++ [((τ, none), false)])
        | some i =>
          if i ∈ remainingResources h ∧ (i, τ) ∈ D.edges then
            D.probability (i, τ) * (D.reward i + onlineContinuation D A k (t+1) (h ++ [((τ, some i), true)])) +
            (1 - D.probability (i, τ)) * onlineContinuation D A k (t+1) (h ++ [((τ, some i), false)])
          else onlineContinuation D A k (t+1) (h ++ [((τ, none), false)])
    else 0

def onlineValue {n m : ℕ} (D : Instance n m) (A : OnlineRule n m) : ℝ :=
  onlineContinuation D A m 0 []

end StochasticRewardMatching.Decomposable


