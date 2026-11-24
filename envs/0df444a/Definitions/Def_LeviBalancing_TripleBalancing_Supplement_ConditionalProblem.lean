-- Prove2me | Definitions.Def_LeviBalancing_TripleBalancing_Supplement_ConditionalProblem
-- name    : LeviBalancing_TripleBalancing_Supplement_ConditionalProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:20:54.333935+00:00
-- url     : https://prove2.me/theorems/f11738ab-7efc-4869-9f94-69c438083f0d
-- title:
--   The conditional Bellman problem over all nonanticipatory future controls
-- statement:
--   Fix a particular period and information state $(s,f_s)$. Its conditional probability law $\nu$ fixes the root information and has finite means for every remaining demand. The source permits arbitrary correlation, nonstationarity, and external information. This is a conditional problem; no unconditional demand-moment assumption is added.
--
--   For a target $y$, the immediate one-lead-time cost is
--
--   $$
--   g_s(y)=E_\nu[h_{s+L}(y-D_{[s,s+L]})^++p_{s+L}(D_{[s,s+L]}-y)^+].
--   $$
--
--   The continuation value $W_s(y)$ is the infimum of expected remaining costs over every feasible adapted future order process. The actual inventory costs are the published period costs; the state after current demand is $y-D_s$. The Bellman action and conditional value are
--
--   $$
--   J_s(y)=g_s(y)+W_s(y),\qquad V_s(x)=\inf_{y\ge x}J_s(y).
--   $$
--
--   The continuation is the full finite-horizon control problem, rather than a surrogate or a restriction to base-stock policies. It is expressed variationally over future plans, unrolling the Bellman recursion. Terminal continuation is zero, and costs after the horizon are omitted. A zero future-order plan is admissible, so the infimum is never over an empty policy class. Costs before $s+L$ are policy-independent for this conditional decision and are omitted from all competitors.
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, pp. 288–290, 298 (PDF 5–7, 15), §2, §3.1, §5.2

import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Supplement_ConditionalCosts

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace LeviBalancing.TripleBalancing.Supplement
open LeviBalancing.DualBalancing

/-- A conditional subproblem rooted at a specified (s,f_s). Integrability is under THIS
conditional probability, not the unconditional law of the original campaign. The root
information is fixed modulo null events. Future information and demand are exogenous and
may have arbitrary correlation and nonstationarity. -/
structure ConditionalProblem (Ω : Type*) [m : MeasurableSpace Ω] (I : Instance) (s : ℤ) where
  ν : Measure Ω
  probability : IsProbabilityMeasure ν
  information : Filtration ℤ m
  process : DemandProcess information ν I.T
  root_fixed : ∀ A : Set Ω, MeasurableSet[information s] A → ν A = 0 ∨ ν A = 1
  conditional_mean : ∀ j, s ≤ j → j ≤ (I.T : ℤ) →
    Integrable (process.D j) ν

/-- All feasible nonanticipatory future controls. Orders up to and including the root period
are zero: the root action is supplied separately. Late orders are zero because they cannot
arrive within the horizon. Zero future orders always give an admissible continuation. -/
def IsFuturePlan {Ω : Type*} [MeasurableSpace Ω] {I : Instance} {s : ℤ}
    (M : ConditionalProblem Ω I s) (A : ℤ → Ω → ℝ) : Prop :=
  IsFeasiblePolicy I M.information A ∧
    (∀ t ω, t ≤ s → A t ω = 0) ∧
    (∀ t ω, (I.T : ℤ) - I.L < t → A t ω = 0)

/-- Actual one-lead-time period cost at position y, using the published dynamics. In this
coordinate chart the root action has already raised the inventory position to y. -/
def localPeriodCost {Ω : Type*} [MeasurableSpace Ω] {I : Instance} {s : ℤ}
    (M : ConditionalProblem Ω I s) (y : ℝ) (A : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  let d := fun j => M.process.D j ω
  periodCost (decisionInstance I d s y) d (fun j => A j ω) (t + I.L)

/-- Immediate cost is charged at s+L. If that date lies outside the horizon, it is zero. -/
def immediateValue {Ω : Type*} [MeasurableSpace Ω] {I : Instance} {s : ℤ}
    (M : ConditionalProblem Ω I s) (y : ℝ) : ℝ≥0∞ :=
  if s + I.L ≤ (I.T : ℤ) then
    ∫⁻ ω, ENNReal.ofReal (localPeriodCost M y (fun _ _ => 0) s ω) ∂M.ν
  else 0

/-- Conditional remaining cost after the root's immediate cost. The state at the next
period is y-D_s; the lead-time shift charges precisely the costs affected by future orders. -/
def continuationCost {Ω : Type*} [MeasurableSpace Ω] {I : Instance} {s : ℤ}
    (M : ConditionalProblem Ω I s) (y : ℝ) (A : ℤ → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (∑ t ∈ Icc (s + 1) ((I.T : ℤ) - I.L),
    localPeriodCost M y A t ω) ∂M.ν

/-- Genuine optimal continuation over ALL adapted future controls, not over base-stock
comparators or the minimizing-policy surrogate. ENNReal infima retain infinite costs. -/
def continuationValue {Ω : Type*} [MeasurableSpace Ω] {I : Instance} {s : ℤ}
    (M : ConditionalProblem Ω I s) (y : ℝ) : ℝ≥0∞ :=
  ⨅ A : ℤ → Ω → ℝ, ⨅ (_ : IsFuturePlan M A), continuationCost M y A

/-- The Bellman action objective: immediate one-lead-time cost plus optimal continuation.
This variational definition is the unrolled finite-horizon recursion of §3.1, with zero
terminal continuation. No Bellman comparison with R^M is assumed. -/
def bellmanAction {Ω : Type*} [MeasurableSpace Ω] {I : Instance} {s : ℤ}
    (M : ConditionalProblem Ω I s) (y : ℝ) : ℝ≥0∞ :=
  immediateValue M y + continuationValue M y

/-- Optimal conditional value for pre-order position x, with the source's constraint y≥x.
Policy-independent pipeline costs before s+L have been omitted from every candidate. -/
def remainingValue {Ω : Type*} [MeasurableSpace Ω] {I : Instance} {s : ℤ}
    (M : ConditionalProblem Ω I s) (x : ℝ) : ℝ≥0∞ :=
  ⨅ y : ℝ, ⨅ (_ : x ≤ y), bellmanAction M y

end LeviBalancing.TripleBalancing.Supplement


