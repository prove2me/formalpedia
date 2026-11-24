-- Prove2me | Definitions.Def_LeviBalancing_TripleBalancing_Supplement_Targets
-- name    : LeviBalancing_TripleBalancing_Supplement_Targets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:22:04.204781+00:00
-- url     : https://prove2.me/theorems/b2c70c29-9d42-4c35-b772-18a6d530c5dc
-- title:
--   The smallest minimizing-policy target and a genuine optimal base-stock target
-- statement:
--   At a specified conditional state $(s,f_s)$, define the target-level objective
--
--   $$
--   F_s(y)=E\!\left[\sum_{j=s+L}^{T}h_j(y-D_{[s,j]})^++p_{s+L}(D_{[s,s+L]}-y)^+\mid f_s\right].
--   $$
--
--   The backlog term is omitted when $s+L>T$. For $y\ge x$, this differs from $\ell_s(y-x)+\pi_s(y-x)$ by a term independent of $y$. A supplied $R^M$ is the smallest global minimizer of $F_s$: it attains its minimum and is no greater than every other minimizer. The feasible action at position $x$ orders up to $\max(x,R^M)$.
--
--   A supplied optimal target $R^{OPT}$ has a different definition: for every starting position $x$, raising inventory to $\max(x,R^{OPT})$ attains the true conditional Bellman value, with an attained continuation among all feasible nonanticipatory future controls.
--
--   These are witness predicates for the targets the source names. Neither defines $R^{OPT}$ using $R^M$ or assumes their ordering. No target is assigned a default when the smallest minimizer or an optimum does not exist. After the last actionable date the surrogate is constant and has no smallest real target.
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, pp. 290, 298 (PDF 7, 15), §3.1, §5.2

import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Supplement_ConditionalProblem

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace LeviBalancing.TripleBalancing.Supplement
open LeviBalancing.DualBalancing

/-- The target-level objective in §5.2. For y≥x, subtracting the y-independent holding cost
of the initial x units gives exactly l_s(y-x)+π_s(y-x). Holding is charged through T;
backlog is charged only at s+L. This is not the one-period myopic objective. -/
def minimizingObjective {Ω : Type*} [MeasurableSpace Ω] {I : Instance} {s : ℤ}
    (M : ConditionalProblem Ω I s) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (
    (∑ j ∈ Icc (s + (I.L : ℤ)) (I.T : ℤ),
      I.h j * max (y - cumDemand (fun t => M.process.D t ω) s j) 0) +
    if s + I.L ≤ (I.T : ℤ) then
      I.p (s + I.L) * max (cumDemand (fun t => M.process.D t ω) s (s + I.L) - y) 0
    else 0) ∂M.ν

/-- A witness of the source's SMALLEST minimizing target, with no default when no least
minimizer exists. The feasible action at inventory x orders up to max x R. -/
def IsSmallestMinimizingTarget {Ω : Type*} [MeasurableSpace Ω] {I : Instance} {s : ℤ}
    (M : ConditionalProblem Ω I s) (R : ℝ) : Prop :=
  (∀ y : ℝ, minimizingObjective M R ≤ minimizingObjective M y) ∧
  (∀ y : ℝ, minimizingObjective M y = minimizingObjective M R → R ≤ y)

/-- An actual optimal state-dependent base-stock target for this conditional subproblem.
For every starting inventory, max x R attains the Bellman value over ALL feasible current
orders, and its optimal future control is attained among all nonanticipatory continuations.
This property does not refer to the minimizing-policy target or its desired lower bound. -/
def IsOptimalBaseStockTarget {Ω : Type*} [MeasurableSpace Ω] {I : Instance} {s : ℤ}
    (M : ConditionalProblem Ω I s) (R : ℝ) : Prop :=
  ∀ x : ℝ, bellmanAction M (max x R) = remainingValue M x ∧
    ∃ A : ℤ → Ω → ℝ, IsFuturePlan M A ∧
      continuationCost M (max x R) A = continuationValue M (max x R)

end LeviBalancing.TripleBalancing.Supplement


