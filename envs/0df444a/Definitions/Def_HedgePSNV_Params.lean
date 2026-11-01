-- Prove2me | Definitions.Def_HedgePSNV_Params
-- name    : HedgePSNV_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:27.825011+00:00
-- url     : https://prove2.me/theorems/a611774e-da49-4e7a-a965-6ccc976d1598
-- title:
--   Parameters, production payoff $H_T(P,R)$ and decision domain $D$ of the price-setting newsvendor
-- statement:
--   The price-setting newsvendor sells over a period $[0,T]$, $T>0$. It chooses a unit price $P$ and a **virtual production quantity** (VPQ) $R=Q+bP$, where $Q$ is the production quantity and $b>0$ the sensitivity of demand $D_T(P)=A_T-bP$ to the price. With unit production cost $c$, unit salvage value $s<c$, and a realized market size $a$, the **production payoff** is
--   $$
--   H_T(P,R)=(P-c)(R-bP)-(P-s)(R-a)^+ .
--   $$
--   The **decision domain** of problem (2) is
--   $$
--   D=\{(P,R):\ P\ge c,\ R-bP\ge 0\}.
--   $$
--   The parameter structure also carries the volatility $\tilde\sigma>0$ of the demand noise in (9) and the initial asset price $x_0>0$.
--
--   Every optimization over $(P,R)$ in the mission (problem (2), the risk-neutral problem of p.21, problem (15) and the section problems (EC.8.2)) is taken over $D$ or over its sections.
--
--   **Formalization Note** $s<c$ is the newsvendor convention for "unit production cost" and "unit salvage value" (p.7) and follows from Assumption 3. Time is $\mathbb R_{\ge0}$. The payoff is a function of the market size $a$, so that it can be evaluated on $A_T$ under any measure.
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, §2, p.7 (payoff, demand $D_T=A_T-bP$); (2)–(3), p.8 (VPQ, decision domain); (9), p.11 ($\tilde\sigma$)

import Mathlib

open scoped NNReal

namespace HedgePSNV

/-- The primitive constants of the price-setting newsvendor with risk hedging,
Wang–Yao–Zhang, *How Does Risk Hedging Impact Operations?*, arXiv:2201.01026v4, §2 p.7 and
§3.1 p.11: the selling horizon `T > 0`, the price sensitivity `b > 0` of demand
(`D_T(P) = A_T − bP`), the unit production cost `c`, the unit salvage value `s < c`, the
demand-noise volatility `σ̃ > 0` in (9), and the initial asset price `x₀ > 0`.

**Formalization Note** `s < c` is the newsvendor convention of "unit production cost" and
"unit salvage value" (p.7); under Assumption 3 it is implied. `x₀ > 0` is the positivity of
an asset price, used in the proof of Theorem 1 (p.ec28). Time is `ℝ≥0`. -/
structure Params where
  T : ℝ≥0
  b : ℝ
  c : ℝ
  s : ℝ
  σt : ℝ
  x₀ : ℝ
  hT : 0 < T
  hb : 0 < b
  hsc : s < c
  hσt : 0 < σt
  hx₀ : 0 < x₀

/-- The production payoff of (P, R) when the market size is `a`, arXiv:2201.01026v4, §2,
p.7 and (3), p.8: with the virtual production quantity `R = Q + bP`,
`H_T(P,R) = (P − c)(R − bP) − (P − s)(R − A_T)^+`. -/
def payoff (p : Params) (P R a : ℝ) : ℝ :=
  (P - p.c) * (R - p.b * P) - (P - p.s) * max (R - a) 0

/-- The decision domain of problem (2), arXiv:2201.01026v4, p.8:
`D = {(P, R) : P ≥ c, R − bP ≥ 0}`. Every arg max and arg min over `(P, R)` in the paper is
read over this set (p.9: the constraints "can be removed … The same applies to all relevant
settings throughout the paper", i.e. they are non-binding constraints of the same problems). -/
def decisionDomain (p : Params) : Set (ℝ × ℝ) :=
  {q | p.c ≤ q.1 ∧ p.b * q.1 ≤ q.2}

end HedgePSNV


