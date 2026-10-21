-- Prove2me | Definitions.Def_DeferredInspection_SingleAgent_Model
-- name    : DeferredInspection_SingleAgent_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T04:57:34.014096+00:00
-- url     : https://prove2.me/theorems/5a1c22c6-c0c8-4401-a813-e8195e3965ee
-- title:
--   §§2–3, pp. 5–12 — deferred-inspection model, payments, bids, and Theorem 2 rules
-- statement:
--   A buyer has private value $v\in V=[0,1]$ with a differentiable, strictly positive density $f$ of total mass one. An allocation rule $x$ gives the probability of receiving the object after reporting a value, and $p(v)$ is the seller's net payment from a truthful type $v$. A false report $w$ forfeits the deposited amount $w$. The incentive constraint is
--
--   $$v x(w)-w\le v x(v)-p(v),\qquad v,w\in V.$$
--
--   Feasibility also requires $0\le x\le1$, nonnegative truthful utility, and an integrable expected payment. Revenue is $\int_0^1p(v)f(v)\,dv$; optimality compares against every feasible allocation and payment pair.
--
--   The module defines the maximum IC payment $p_x$ from (10), its revenue objective, the concave hull of $x$, the largest best-alternative minimizer $b_x$ from (12), and the SCD class. It also defines $G(t)=\int_0^t yf(y)\,dy$, its lower inverse, and the explicit bid, allocation, and payment functions of Theorem 2.
--
--   **Formalization Note** Values outside $V$ are irrelevant. Real infima and suprema are used only where the source's feasible sets are nonempty and bounded. The threshold equation $x(\bar v)=1$ is interpreted through the integral branch, giving continuity at $\bar v$.
-- source:
--   Alaei, Belloni, Makhdoumi & Malekian, SSRN 3700525 (version of 2022-03-22), pp. 5–12, Assumption 1, Problem (7)–(9), (10)–(13), Theorem 2

import Mathlib

namespace DeferredInspection.SingleAgent

open MeasureTheory Set Filter Topology

/-- Assumption 1, p. 5: a differentiable, positive probability density on the value interval. -/
def Assumption1 (f : ℝ → ℝ) : Prop :=
  DifferentiableOn ℝ f (Icc 0 1) ∧
    (∀ v ∈ Icc (0 : ℝ) 1, 0 < f v) ∧
    ∫ v in (0 : ℝ)..1, f v = 1

/-- An allocation probability on the value interval, §2, p. 5. -/
def IsAllocation (x : ℝ → ℝ) : Prop :=
  ∀ v ∈ Icc (0 : ℝ) 1, x v ∈ Icc (0 : ℝ) 1

/-- IC (8), p. 7. A false report `w` forfeits deposit `w`. -/
def IsIC (x p : ℝ → ℝ) : Prop :=
  ∀ v ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1,
    v * x w - w ≤ v * x v - p v

/-- Individual rationality (9), p. 7. -/
def IsIR (x p : ℝ → ℝ) : Prop :=
  ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ v * x v - p v

/-- Expected payment (7), p. 7. -/
noncomputable def revenue (f p : ℝ → ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, p v * f v

/-- Feasibility for (7)–(9), with the integrability needed for expected payment. -/
def IsFeasible (f x p : ℝ → ℝ) : Prop :=
  IsAllocation x ∧ IsIC x p ∧ IsIR x p ∧
    IntervalIntegrable (fun v => p v * f v) volume 0 1

/-- Global optimality among every feasible mechanism in (7)–(9). -/
def IsOptimal (f x p : ℝ → ℝ) : Prop :=
  IsFeasible f x p ∧
    ∀ x' p' : ℝ → ℝ, IsFeasible f x' p' → revenue f p' ≤ revenue f p

/-- Optimal payment for an allocation, (10), p. 7. -/
noncomputable def optPay (x : ℝ → ℝ) (v : ℝ) : ℝ :=
  sInf ((fun w => v * (x v - x w) + w) '' Icc 0 v)

/-- Revenue objective for an allocation, (11), p. 8. -/
noncomputable def allocRevenue (f x : ℝ → ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, optPay x v * f v

/-- The pointwise least concave majorant of an allocation, Lemma 1(2), p. 8. -/
noncomputable def concaveHull (x : ℝ → ℝ) (v : ℝ) : ℝ :=
  sInf {y | ∃ g : ℝ → ℝ, ConcaveOn ℝ (Icc 0 1) g ∧
    (∀ w ∈ Icc (0 : ℝ) 1, x w ≤ g w) ∧ y = g v}

/-- The largest minimizer in the best-alternative-bid definition (12), p. 9. -/
noncomputable def bestAltOf (x : ℝ → ℝ) (v : ℝ) : ℝ :=
  sSup {u | u ∈ Icc 0 v ∧
    IsMinOn (fun w => v * (x v - x w) + w) (Icc 0 v) u}

/-- SCD allocations with threshold `vh`, p. 10. -/
def IsSCD (x : ℝ → ℝ) (vh : ℝ) : Prop :=
  IsAllocation x ∧ vh ∈ Icc (0 : ℝ) 1 ∧
    StrictConcaveOn ℝ (Icc 0 vh) x ∧
    DifferentiableOn ℝ x (Icc 0 vh) ∧
    x 0 = 0 ∧ ∀ v ∈ Icc vh 1, x v = 1

/-- Weighted cumulative value `G(t)`, p. 11. -/
noncomputable def G (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..t, y * f y

/-- `G⁻¹` on the range of `G`, as its lower inverse on `[0,1]`, p. 12. -/
noncomputable def Ginv (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  sInf {y | y ∈ Icc (0 : ℝ) 1 ∧ s ≤ G f y}

/-- Theorem 2's best-alternative bid `b`, p. 12. -/
noncomputable def bidFn (f : ℝ → ℝ) (vl v : ℝ) : ℝ :=
  if v ≤ vl then 0 else Ginv f (G f v - G f vl)

/-- The inverse expression `b⁻¹(v) = G⁻¹(G(v) + G(vl))`, p. 12. -/
noncomputable def bidFnInv (f : ℝ → ℝ) (vl v : ℝ) : ℝ :=
  Ginv f (G f v + G f vl)

/-- Theorem 2's allocation rule, p. 12. -/
noncomputable def optAlloc (f : ℝ → ℝ) (vl vh v : ℝ) : ℝ :=
  if vh ≤ v then 1
  else ∫ t in vl..bidFnInv f vl v, deriv (bidFn f vl) t / t

/-- Theorem 2's three-branch payment rule, p. 12. -/
noncomputable def optPayment (f : ℝ → ℝ) (vl vh v : ℝ) : ℝ :=
  if v ≤ vl then v * optAlloc f vl vh v
  else if v < vh then
    v * (optAlloc f vl vh v - optAlloc f vl vh (bidFn f vl v)) + bidFn f vl v
  else v * (1 - optAlloc f vl vh (bidFn f vl v)) + bidFn f vl v

/-- Theorem 2's two threshold equations, with `x(vh)=1` read through the integral branch. -/
def BoundaryConds (f : ℝ → ℝ) (vl vh : ℝ) : Prop :=
  vl ∈ Icc (0 : ℝ) 1 ∧ vh = bidFn f vl 1 ∧
    ∫ t in vl..bidFnInv f vl vh, deriv (bidFn f vl) t / t = 1

end DeferredInspection.SingleAgent


