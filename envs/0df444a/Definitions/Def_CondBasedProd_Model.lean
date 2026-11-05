-- Prove2me | Definitions.Def_CondBasedProd_Model
-- name    : CondBasedProd_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:44.795502+00:00
-- url     : https://prove2.me/theorems/5884e3d7-2c18-4da9-ac20-600f31577cb2
-- title:
--   The production system: failure level, rates, deterioration, revenue and maintenance cost (Assumption 1)
-- statement:
--   A single production system deteriorates through the levels $\mathcal X=\{0,1,\dots,\xi\}$ and fails at level $\xi\in\mathbb N$. The production rate is chosen from $\mathcal S=[0,\bar s]$ with $0<\bar s<\infty$. Under rate $s$ and base rate $\lambda$, deterioration increments arrive at rate $\lambda f(s)$ and revenue accrues at rate $r(s)$. At the planned maintenance moment a cost $c_m(x)$ is charged.
--
--   The standing assumptions are:
--
--   1. (Assumption 1) $f$ and $r$ are continuous and increasing on $\mathcal S$, with $f(0)=0$ and $r(0)\le 0$;
--   2. $c_m\ge 0$ on $\mathcal X$, increasing, and convex: $c_m(x+1)-c_m(x)\le c_m(x+2)-c_m(x+1)$ for $x+2\le\xi$.
--
--   "Increasing" is meant in the weak sense. Every result of the mission is stated for all such models, including $r(0)<0$.
--
--   **Formalization Note** $f$, $r$ are total functions on $\mathbb R$ and $c_m$ on $\mathbb N$, constrained only on $\mathcal S$ and $\mathcal X$. The codomain $\mathbb R_+$ of $f$ follows from monotonicity and $f(0)=0$.
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, §3, pp.8–9, Assumption 1, p.9

import Mathlib

open Set

namespace CondBasedProd

/-- **The production system** (Drent, Drent & Arts, *Condition-Based Production for Stochastically
Deteriorating Systems*, arXiv:2308.07507v2, §3, pp.8–9, Assumption 1, p.9).

Deterioration levels are `𝒳 = {0, 1, …, ξ}`, with failure at level `ξ`; production rates are
`𝒮 = [0, s̄]`, `0 < s̄ < ∞`. Under rate `s` the deterioration rate is `λ f(s)` and the revenue rate
is `r(s)`. **Assumption 1**: `f` and `r` are continuous and increasing (in the weak sense, p.9),
`f(0) = 0` and `r(0) ≤ 0`. The maintenance cost `c_m : 𝒳 → ℝ₊` is increasing and convex (p.9).

**Formalization Note.** `f`, `r` are total functions on `ℝ` and `c_m` on `ℕ`, constrained only on
`𝒮` and `𝒳`; no value outside these sets is ever read. `f ≥ 0` on `𝒮` (the codomain `ℝ₊` on p.8) follows
from `f_mono` and `f_zero` and is not a field. `ξ = 0` is allowed (p.8 says only `ξ ∈ ℕ`). `r(0) < 0`
is allowed (Remark 2, p.9). -/
structure Model where
  /-- The failure level `ξ`. -/
  ξ : ℕ
  /-- The maximum production rate `s̄`. -/
  sbar : ℝ
  /-- The deterioration function `f`. -/
  f : ℝ → ℝ
  /-- The revenue function `r`. -/
  r : ℝ → ℝ
  /-- The maintenance cost function `c_m`. -/
  cm : ℕ → ℝ
  sbar_pos : 0 < sbar
  f_cont : ContinuousOn f (Icc 0 sbar)
  f_mono : MonotoneOn f (Icc 0 sbar)
  f_zero : f 0 = 0
  r_cont : ContinuousOn r (Icc 0 sbar)
  r_mono : MonotoneOn r (Icc 0 sbar)
  r_zero_le : r 0 ≤ 0
  cm_nonneg : ∀ x ≤ ξ, 0 ≤ cm x
  cm_mono : ∀ x < ξ, cm x ≤ cm (x + 1)
  cm_convex : ∀ x, x + 2 ≤ ξ → cm (x + 1) - cm x ≤ cm (x + 2) - cm (x + 1)

end CondBasedProd


