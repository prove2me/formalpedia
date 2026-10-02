-- Prove2me | Definitions.Def_ServiceParts_BaseStock_Model
-- name    : ServiceParts_BaseStock_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T21:20:45.086856+00:00
-- url     : https://prove2.me/theorems/eee77d36-d274-4317-a754-a52b53a31f1d
-- title:
--   Periodic-review backorder model with linear costs and a positive continuous demand density
-- statement:
--   A single item is stocked at a single location and reviewed periodically. Orders placed at the start of a period arrive at the start of the next period (lead time $\tau = 1$), demand not met from stock is backordered, and costs are linear:
--
--   1. $c \ge 0$ is the unit purchase cost, charged on the quantity ordered;
--   2. $h > 0$ is the holding cost per unit on hand at the end of a period;
--   3. $b$ is the backorder cost per unit backordered at the end of a period;
--   4. $\alpha \in (0,1)$ is the discount factor.
--
--   Demand is independent from period to period, with a density $g$ on $(0,\infty)$ that is positive and continuous there, integrates to one, and has a finite mean:
--   $$
--   g(x) > 0 \ (x > 0), \qquad \int_0^\infty g(x)\,dx = 1, \qquad \int_0^\infty x\,g(x)\,dx < \infty.
--   $$
--   Finally the backorder cost is assumed to outweigh the gain from deferring a purchase by one period:
--   $$
--   b > \frac{1-\alpha}{\alpha}\,c .
--   $$
--
--   The one-period expected holding and backorder cost when the net inventory at the start of the period is $y$ is
--   $$
--   L(y) = \begin{cases} h\displaystyle\int_0^y (y-x)\,g(x)\,dx + b\int_y^\infty (x-y)\,g(x)\,dx, & y > 0,\\[2mm] b\displaystyle\int_0^\infty (x-y)\,g(x)\,dx, & y \le 0. \end{cases}
--   $$
--
--   This is the model of Section 2.1 on which every statement of the mission is built.
--
--   **Formalization Note** Every standing assumption is a field of the structure, so each theorem of the mission carries all of them. The signs $c \ge 0$ and $h > 0$ are not written in the book, which only calls $c$ and $h$ unit costs; $h > 0$ is what its proof uses when it asserts $\lim_{w\to\infty} f_n'(w-x) > 0$ (p. 20). The finite mean is added because $L$ is finite only when $E[D] < \infty$. Independence of demands is implicit: the recursion integrates each period's demand against the same density $g$. $b > 0$ follows from the last displayed assumption.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 16-17 and p. 19, Section 2.1 (model, L(y), and the assumption b > ((1 - alpha)/alpha) c)

import Mathlib

open MeasureTheory Set

namespace ServiceParts.BaseStock

/-- The single-location, periodic-review, backorder model of Muckstadt (2005), Section 2.1,
pp. 16–19, with its standing assumptions: unit purchase cost `c`, unit holding cost `h`,
unit backorder cost `b`, discount factor `α`, and a demand density `g` on `(0, ∞)` that is
positive and continuous there, integrates to one, and has a finite mean. -/
structure Model where
  /-- unit purchase cost -/
  c : ℝ
  /-- unit holding cost per period -/
  h : ℝ
  /-- unit backorder cost per period -/
  b : ℝ
  /-- discount factor -/
  α : ℝ
  /-- demand density on `(0, ∞)` -/
  g : ℝ → ℝ
  c_nonneg : 0 ≤ c
  h_pos : 0 < h
  α_pos : 0 < α
  α_lt_one : α < 1
  /-- "To make the problem interesting, we assume that b > ((1 − α)/α) c" (p. 19). -/
  b_gt : (1 - α) / α * c < b
  g_pos : ∀ x : ℝ, 0 < x → 0 < g x
  g_cont : ContinuousOn g (Ioi 0)
  g_total : ∫ x in Ioi (0 : ℝ), g x = 1
  g_mean : IntegrableOn (fun x : ℝ => x * g x) (Ioi 0)

/-- The expected one-period holding and backorder cost `L(y)` of p. 17, when `y` units are
on hand (net) at the beginning of the period and the period's demand has density `g`. -/
noncomputable def Model.L (M : Model) (y : ℝ) : ℝ :=
  if 0 < y then
    M.h * (∫ x in Ioc (0 : ℝ) y, (y - x) * M.g x) + M.b * (∫ x in Ioi y, (x - y) * M.g x)
  else
    M.b * ∫ x in Ioi (0 : ℝ), (x - y) * M.g x

end ServiceParts.BaseStock


