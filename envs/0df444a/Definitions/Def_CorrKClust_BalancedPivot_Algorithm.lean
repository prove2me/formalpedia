-- Prove2me | Definitions.Def_CorrKClust_BalancedPivot_Algorithm
-- name    : CorrKClust_BalancedPivot_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:01.333779+00:00
-- url     : https://prove2.me/theorems/990f4c9e-dc9a-48a9-8e88-706c79c0e8c2
-- title:
--   Sequential PIVOT and Algorithm 1 with every admissible tie rule
-- statement:
--   Process an arrival list in order, maintaining the chronologically ordered list of pivots. A vertex with an earlier pivot neighbour joins the cluster of its earliest such neighbour. Otherwise it becomes a new pivot. PIVOT gives this pivot its own representative label. BALANCED PIVOT maintains $k\ge1$ output clusters and assigns the new pivot to a cluster with minimum current vertex count:
--   $$b=\rho(h,f,v),\qquad |\{u\in h:f(u)=b\}|\le |\{u\in h:f(u)=b'\}|\quad\text{for every }b'.$$
--   Here $h$ is the already processed arrival history, $f$ is the current assignment and $v$ is the incoming vertex. The rule $\rho$ may depend on all these data. Both algorithms are defined by folds over the actual arrival prefix, with no optimum oracle and no cost guarantee in their definitions.
--
--   The current load counts arrived vertices only. The initial assignment gives unarrived vertices an irrelevant default label; every arriving vertex is explicitly assigned. The admissibility predicate is imposed on all histories, so an online minimum-size choice on reachable states can be extended arbitrarily by a minimum-size choice elsewhere. The theorem quantifies over every admissible rule.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), PIVOT description; §7.1; Algorithm 1, pp. 2–29, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Mathlib
import Definitions.Def_CorrKClust_BalancedPivot_Instance
import Definitions.Def_CorrKClust_BalancedPivot_Orders

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Chronological pivot list and the representative of each arrived vertex. -/
structure PivotState (V : Type*) where
  pivots : List V
  root : V → V

def pivotStep {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (s : PivotState V) (v : V) : PivotState V :=
  match s.pivots.find? (fun p => decide (G.Adj v p)) with
  | some p => ⟨s.pivots, Function.update s.root v p⟩
  | none => ⟨s.pivots ++ [v], Function.update s.root v v⟩

/-- Actual sequential PIVOT, using the earliest adjacent pivot. -/
def pivotRun {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (σ : ArrivalOrder V) (t : ℕ) : PivotState V :=
  ((arrivalList σ).take t).foldl (pivotStep G) ⟨[], id⟩

def pivotAssignment {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (σ : ArrivalOrder V) : V → V :=
  (pivotRun G σ (Fintype.card V)).root

def pivots {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (σ : ArrivalOrder V) : Finset V :=
  (pivotRun G σ (Fintype.card V)).pivots.toFinset

/-- A history-dependent choice, with no access to the unrevealed arrival suffix. -/
abbrev TieRule (V : Type*) (k : ℕ) := List V → (V → Fin k) → V → Fin k

def historyLoad {V : Type*} {k : ℕ} (h : List V) (f : V → Fin k) (b : Fin k) : ℕ :=
  (h.filter (fun v => f v = b)).length

/-- Algorithm 1 line 10, uniform over every minimum-size choice. -/
def Admissible {V : Type*} {k : ℕ} (ρ : TieRule V k) : Prop :=
  ∀ h f v b, historyLoad h f (ρ h f v) ≤ historyLoad h f b

structure BalancedState (V : Type*) (k : ℕ) where
  seen : List V
  pivots : List V
  assignment : V → Fin k

/-- Each transition uses only the current arrival and earlier pivots and assignments. -/
def balancedStep {V : Type*} [DecidableEq V] {k : ℕ} (G : SimpleGraph V)
    (ρ : TieRule V k) (s : BalancedState V k) (v : V) : BalancedState V k :=
  match s.pivots.find? (fun p => decide (G.Adj v p)) with
  | some p => ⟨s.seen ++ [v], s.pivots, Function.update s.assignment v (s.assignment p)⟩
  | none => ⟨s.seen ++ [v], s.pivots ++ [v],
      Function.update s.assignment v (ρ s.seen s.assignment v)⟩

/-- Algorithm 1 is a fold, initialized with all k clusters empty. The initial label of an
unarrived vertex is irrelevant; every arrived vertex is explicitly assigned in the step. -/
def balancedRun {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 0 < k)
    (G : SimpleGraph V) (ρ : TieRule V k) (σ : ArrivalOrder V) (t : ℕ) : BalancedState V k :=
  ((arrivalList σ).take t).foldl (balancedStep G ρ) ⟨[], [], fun _ => ⟨0, hk⟩⟩

def balancedAssignment {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 0 < k)
    (G : SimpleGraph V) (ρ : TieRule V k) (σ : ArrivalOrder V) : V → Fin k :=
  (balancedRun hk G ρ σ (Fintype.card V)).assignment

end CorrKClust.BalancedPivot


