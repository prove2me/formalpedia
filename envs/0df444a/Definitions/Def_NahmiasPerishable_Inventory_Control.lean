-- Prove2me | Definitions.Def_NahmiasPerishable_Inventory_Control
-- name    : NahmiasPerishable_Inventory_Control
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:23:45.591555+00:00
-- url     : https://prove2.me/theorems/dac51a52-6fcc-47f9-8a48-504233927d69
-- title:
--   Perishable inventory: Control
-- statement:
--   Demand-driven Bellman value, first-action objective, attaining minimizer, and defined expected-cost predicate. Infima are taken in EReal over nonnegative real orders; no convexity, attainment, or regularity is assumed in the data.
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, pp. 683, 686, DOI:10.1287/opre.30.4.680.

import Definitions.Def_NahmiasPerishable_Inventory_Demand

open MeasureTheory Set
noncomputable section

namespace NahmiasPerishable.Inventory

/-- A finite-horizon shock-driven control problem with nonnegative real actions.
The terminal value is data, not a regularity or optimality axiom. -/
structure ShockControl (X : Type*) where
  shock : Measure ℝ
  transfer : X → ℝ → ℝ → X
  stage : X → ℝ → EReal
  terminal : X → EReal
  discount : ℝ

/-- Bellman infimum in EReal, with no assumption of attainment. -/
def ShockControl.value {X : Type*} (M : ShockControl X) : ℕ → X → EReal
  | 0, x => M.terminal x
  | n+1, x => ⨅ y : {y : ℝ // 0 ≤ y},
      M.stage x y + (M.discount : EReal) *
        expectation M.shock (fun d => M.value n (M.transfer x y d))

def ShockControl.objective {X : Type*} (M : ShockControl X) (n : ℕ) (x : X) (y : ℝ) : EReal :=
  M.stage x y + (M.discount : EReal) * expectation M.shock (fun d => M.value n (M.transfer x y d))

def ShockControl.optimal {X : Type*} (M : ShockControl X) (n : ℕ) (x : X) (y : ℝ) : Prop :=
  0 ≤ y ∧ M.objective n x y = M.value (n+1) x

/-- The expected-cost convention: the integrals in the displayed recursion must be defined. -/
def ShockControl.defined {X : Type*} (M : ShockControl X) (feasible : Set X) : Prop :=
  ∀ n x, x ∈ feasible → ∀ y, 0 ≤ y →
    ExpectationDefined M.shock (fun d => M.value n (M.transfer x y d))

/-- Jensen form of convexity valid also for extended costs. -/
def ConvexCost (f : ℝ → EReal) : Prop :=
  ∀ u v a : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ a → a ≤ 1 →
    f (a*u+(1-a)*v) ≤ (a : EReal)*f u + ((1-a : ℝ) : EReal)*f v

end NahmiasPerishable.Inventory


