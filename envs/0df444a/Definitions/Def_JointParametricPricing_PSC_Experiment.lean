-- Prove2me | Definitions.Def_JointParametricPricing_PSC_Experiment
-- name    : JointParametricPricing_PSC_Experiment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:46:39.032904+00:00
-- url     : https://prove2.me/theorems/d10a4ce9-9ac4-4932-bc36-c02af1d590a8
-- title:
--   Finite-outcome sequential experiments and their expectations
-- statement:
--   A sequential experiment has an arbitrary action space, parameter space, and finite outcome space, with nonnegative conditional masses summing to one for every action and parameter. A deterministic policy maps the history of actions and outcomes to its next action. The induced mass of an outcome string is the product of the masses at the recursively selected actions. Expectations sum realized path payoffs with these masses. Histories are stored most recent first. This is conditional sampling under adaptive actions, without asserting unconditional independence. The finite outcome representation places no restriction on the cardinality of the action space.
-- source:
--   Chen, Jasin and Duenyas (2021), Technical Note—Joint Learning and Optimization of Multi-Product Pricing with Finite Resource Capacity and Unknown Demand Parameters, DOI:10.1287/opre.2020.2078; held LBS manuscript/online appendix (published citation basis); §2, printed 6–7 / PDF 7–8; sequential-law substrate

import Definitions.Def_JointParametricPricing_PSC_Optimization

open scoped BigOperators
noncomputable section

namespace JointParametricPricing.PSC

/-- A finite-outcome sequential experiment, allowing arbitrary action spaces. -/
structure FiniteExperiment (Action Outcome Parameter : Type*) [Fintype Outcome] where
  mass : Action → Parameter → Outcome → ℝ
  nonneg : ∀ a θ y, 0 ≤ mass a θ y
  total : ∀ a θ, ∑ y, mass a θ y = 1

namespace FiniteExperiment
variable {Action Outcome Parameter : Type*} [Fintype Outcome]
/-- Histories include actions as well as observations; the rule is nonanticipating. -/
abbrev Policy := List (Action × Outcome) → Action

def history (π : Policy (Action := Action) (Outcome := Outcome)) : List Outcome → List (Action × Outcome)
  | [] => []
  | y :: ys => (π (history π ys), y) :: history π ys

/-- Outcome lists are stored most recent first. -/
def pathMass (E : FiniteExperiment Action Outcome Parameter)
    (π : Policy (Action := Action) (Outcome := Outcome)) (θ : Parameter) : List Outcome → ℝ
  | [] => 1
  | y :: ys => pathMass E π θ ys * E.mass (π (history π ys)) θ y

def expectation (E : FiniteExperiment Action Outcome Parameter)
    (π : Policy (Action := Action) (Outcome := Outcome)) (θ : Parameter) (N : ℕ)
    (f : List (Action × Outcome) → ℝ) : ℝ :=
  ∑ y : Fin N → Outcome, E.pathMass π θ (List.ofFn y) * f (history π (List.ofFn y))
end FiniteExperiment
end JointParametricPricing.PSC


