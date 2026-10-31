-- Prove2me | Definitions.Def_MinBuying_Analytic
-- name    : MinBuying_Analytic
-- status  : Definition
-- author  : @mikeh
-- created : 2026-10-30T16:14:12.017421+00:00
-- url     : https://prove2.me/theorems/8ec2dd67-9929-4a97-9774-e084656437eb
-- title:
--   Exact ODE benchmark and critical approximation constant
-- statement:
--   Defines $A(x)=-\log(1-x^2)/x$ with $A(0)=0$, its explicit slope with value $1$ at zero, and the integrating-factor formula for $c$. The exact constant $x^\star$ is the infimum of the set of roots of $xc(x)=1$ restricted to $(0,1)$. Root existence and uniqueness are proof obligations, not assumptions; the main goal asserts them explicitly. Also defines continuous evolution from an arbitrary initial state.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . Eq.(10) p.17; proof of Lemma 3, PDF pp.38–42 / ec11–ec15.

import Mathlib

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace MinBuying

/-- Cumulative budget from equation (10), extended at zero by continuity.
Only its restriction to `[0,1)` enters the formal statements. -/
def canonicalBudget (x : ℝ) : ℝ :=
  if x = 0 then 0 else -Real.log (1 - x ^ 2) / x

/-- Explicit derivative of `canonicalBudget`, with its continuous value at zero. -/
def budgetSlope (x : ℝ) : ℝ :=
  if x = 0 then 1 else 2 / (1 - x ^ 2) + Real.log (1 - x ^ 2) / x ^ 2

/-- Exponent in the integrating factor for the benchmark's linear ODE. -/
def odeExponent (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, t * budgetSlope t

/-- The concrete integrating-factor solution of equation (10).
The equation and initial condition are conclusions of the analytic milestone,
not assumptions incorporated into this definition. -/
def continuousBenchmark (x : ℝ) : ℝ :=
  Real.exp (-odeExponent x) *
    (1 + ∫ t in (0 : ℝ)..x, budgetSlope t * Real.exp (odeExponent t))

/-- The roots considered in the paper are explicitly restricted to `(0,1)`. -/
def criticalRoots : Set ℝ :=
  {x | x ∈ Ioo (0 : ℝ) 1 ∧ x * continuousBenchmark x = 1}

/-- The paper's exact approximation constant. The analytic milestone proves
that the root set is a singleton contained in `(0,1)`, so this infimum does
not rely on Lean's default value for an empty or unbounded-below set. -/
def criticalRatio : ℝ := sInf criticalRoots

/-- Continuous benchmark evolution from state `z` at position `y`.
The relevant domain is `0 ≤ y ≤ x < 1`. -/
def benchmarkFlow (y z x : ℝ) : ℝ :=
  Real.exp (-(odeExponent x - odeExponent y)) *
    (z + ∫ t in y..x,
      budgetSlope t * Real.exp (odeExponent t - odeExponent y))

end MinBuying


