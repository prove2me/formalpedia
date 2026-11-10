-- Prove2me | Definitions.Def_MTSActionPredictions_SyncRestart_Model
-- name    : MTSActionPredictions_SyncRestart_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:57:25.762308+00:00
-- url     : https://prove2.me/theorems/f070e6c5-b6a6-4c36-99bb-4082651fb4f1
-- title:
--   General MTS tasks, costs, causal algorithms, and strict short-input competitiveness
-- statement:
--   Let $(M,d)$ be any metric space. A model specifies a collection of allowed tasks $c:M\to[0,\infty]$. A finite input is valid when each task belongs to that collection. For a trajectory $O$ starting at $x$, its cost and the error of predictions $P$ are
--
--   $$C(O)=\sum_{t=1}^T(d(O_{t-1},O_t)+c_t(O_t)),\qquad \eta(P,O)=\sum_{t=1}^T d(P_t,O_t).$$
--
--   A causal base rule takes a private seed, a restart state and a revealed task prefix, and returns its service state. Its initial state and resulting trajectory determine its cost. Scalar measurability is required only on allowed task histories, for the base cost and distances from its terminal state to fixed states. Strict short-sequence competitiveness means that from every restart state and on every valid sequence of length at most $H$, the expected base cost is at most $\rho$ times every comparator cost from that state, without an additive term.
--
--   These definitions supply the general MTS model, action error, randomized causal interface, and the genuine input hypothesis for the transformation. No competitive conclusion is built into the operational rule.
--
--   Differences from the source:
--   - encoding: nonnegative extended service costs, movement distances, and expectations → ENNReal tasks, metric edist, and nonnegative extended integrals; reason: the same costs and infinities are retained, without conversion to real numbers
--   - encoding: requests indexed from 1 through T and trajectories starting at time 0 → a finite task list with entry i at time i+1 and trajectories on natural times; reason: only the first T+1 states are used, so every finite horizon including zero is represented
--   - encoding: a causal randomized base algorithm initialized at each restart → a seed-indexed rule on a restart state and its revealed task prefix, with scalar measurability on allowed histories; reason: this represents private randomness and defined scalar expectations without imposing topological measurability of tasks or the state space
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; §1.1, PDF pp. 2–3 / printed pp. 1–2; §3 proof, PDF p. 8 / printed p. 7

import Mathlib

open scoped ENNReal BigOperators
open MeasureTheory

namespace MTSActionPredictions.SyncRestart

/-- Section 1.1, PDF 2 / printed 1: arbitrary extended nonnegative tasks. -/
abbrev Task (M : Type*) := M → ℝ≥0∞

/-- A problem's allowed tasks on its supplied arbitrary metric space. -/
structure Model (M : Type*) where
  allowed : Set (Task M)

def ValidTasks {M : Type*} (model : Model M) (q : List (Task M)) : Prop :=
  ∀ c ∈ q, c ∈ model.allowed

/-- Time zero is included in the trajectory; task list entry i is request i+1. -/
noncomputable def trajectoryCost {M : Type*} [MetricSpace M]
    (q : List (Task M)) (O : ℕ → M) : ℝ≥0∞ :=
  ∑ i : Fin q.length, (edist (O i.val) (O (i.val + 1)) + (q.get i) (O (i.val + 1)))

noncomputable def predictionError {M : Type*} [MetricSpace M]
    (T : ℕ) (P O : ℕ → M) : ℝ≥0∞ :=
  ∑ i : Fin T, edist (P (i.val + 1)) (O (i.val + 1))

/-- A fixed private seed, restart state, and revealed prefix determine the action.
There is no access to the comparator, predictions, or future requests. -/
abbrev Rule (Ω M : Type*) := Ω → M → List (Task M) → M

noncomputable def baseTrajectory {Ω M : Type*} (A : Rule Ω M)
    (ω : Ω) (x : M) (q : List (Task M)) (t : ℕ) : M :=
  if t = 0 then x else A ω x (q.take t)

noncomputable def baseCost {Ω M : Type*} [MetricSpace M]
    (A : Rule Ω M) (ω : Ω) (x : M) (q : List (Task M)) : ℝ≥0∞ :=
  trajectoryCost q (baseTrajectory A ω x q)

/-- Only scalar random costs need be measurable. No measurable structure or
separability condition is imposed on M, and tasks can be arbitrary functions. -/
def ScalarMeasurable {Ω M : Type*} [MeasurableSpace Ω] [MetricSpace M]
    (model : Model M) (A : Rule Ω M) : Prop :=
  (∀ x q, ValidTasks model q → Measurable (fun ω => baseCost A ω x q)) ∧
  (∀ x q y, ValidTasks model q → Measurable (fun ω => edist (baseTrajectory A ω x q q.length) y))

/-- The genuine strict short-input hypothesis, uniform over every restart state
and every comparator from that state, with no additive constant. -/
def StrictCompetitive {Ω M : Type*} [MeasurableSpace Ω] [MetricSpace M]
    (model : Model M) (μ : Measure Ω) (A : Rule Ω M) (H : ℕ) (ρ : ℝ) : Prop :=
  ∀ (x : M) (q : List (Task M)), ValidTasks model q → q.length ≤ H →
    ∀ O : ℕ → M, O 0 = x →
      (∫⁻ ω, baseCost A ω x q ∂μ) ≤ ENNReal.ofReal ρ * trajectoryCost q O

end MTSActionPredictions.SyncRestart


