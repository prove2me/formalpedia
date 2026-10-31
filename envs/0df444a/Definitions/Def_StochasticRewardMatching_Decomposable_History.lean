-- Prove2me | Definitions.Def_StochasticRewardMatching_Decomposable_History
-- name    : StochasticRewardMatching_Decomposable_History
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:14:42.102466+00:00
-- url     : https://prove2.me/theorems/92936e75-a844-4c2c-ada9-69c7471360b0
-- title:
--   Observed actions, remaining resources, and legal benchmark actions
-- statement:
--   An action specifies an arrival and either a resource to offer or an explicit discard. Histories record those actions and their observed Boolean outcomes. A discard has probability and reward zero and outcome false. Every processed arrival leaves the remaining-arrival set, while a resource leaves the remaining-resource set only following success. A legal offer uses a present edge and a remaining resource. In ordered mode only the earliest remaining arrival may be processed; in fully offline mode any remaining arrival may be processed. The after-success update deletes only the offered resource.
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), §§1–2, PDF/printed pp. 2–3, 8–9; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_EdgeLaw

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

abbrev Action (n m : ℕ) := Fin m × Option (Fin n)
abbrev History (n m : ℕ) := List (Action n m × Bool)

def remainingArrivals {n m : ℕ} (h : History n m) : Finset (Fin m) :=
  Finset.univ \ (h.map (fun z => z.1.1)).toFinset

def remainingResources {n m : ℕ} (h : History n m) : Finset (Fin n) :=
  Finset.univ \ (h.filterMap (fun z => if z.2 then z.1.2 else none)).toFinset

def legalActions {n m : ℕ} (D : Instance n m) (ordered : Bool)
    (S : Finset (Fin n)) (U : Finset (Fin m)) : Finset (Action n m) := by
  classical
  exact Finset.univ.filter fun a => a.1 ∈ U ∧
    (ordered = true → ∀ t ∈ U, a.1 ≤ t) ∧
    match a.2 with
    | none => True
    | some i => i ∈ S ∧ (i, a.1) ∈ D.edges

def actionBit {n m : ℕ} (D : Instance n m) (ω : Outcome D) (a : Action n m) : Bool :=
  match a.2 with | none => false | some i => bit D ω (i, a.1)

def actionProbability {n m : ℕ} (D : Instance n m) (a : Action n m) : ℝ :=
  match a.2 with | none => 0 | some i => D.probability (i, a.1)

def actionReward {n m : ℕ} (D : Instance n m) (a : Action n m) : ℝ :=
  match a.2 with | none => 0 | some i => D.reward i

def afterSuccess {n m : ℕ} (S : Finset (Fin n)) (a : Action n m) : Finset (Fin n) :=
  match a.2 with | none => S | some i => S.erase i

end StochasticRewardMatching.Decomposable


