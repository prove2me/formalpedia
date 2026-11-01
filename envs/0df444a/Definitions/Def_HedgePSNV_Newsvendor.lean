-- Prove2me | Definitions.Def_HedgePSNV_Newsvendor
-- name    : HedgePSNV_Newsvendor
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:58.963231+00:00
-- url     : https://prove2.me/theorems/3fdc0532-733b-4db0-a6de-a21f1f7bbedf
-- title:
--   Expected payoff, newsvendor maximizer and Assumptions 1–3
-- statement:
--   For a market size $A$ on a measure space $(\Omega,Q)$ the **expected production payoff** is
--   $$
--   \mathbb E_Q[H_T(P,R)]=(P-c)(R-bP)-(P-s)\,\mathbb E_Q[(R-A)^+] \qquad (3).
--   $$
--   With $Q=\mathbb P$ and $A=A_T$ this is the newsvendor's objective; with $Q=\mathbb P^M$ it is $V_0(P,R)$; with $\Omega=\mathbb R$ and $A=\mathrm{id}$ it is the value for a market-size law.
--
--   $(P,R)$ is a **newsvendor maximizer** when $(P,R)\in D$ and $\mathbb E_Q[H_T(P',R')]\le\mathbb E_Q[H_T(P,R)]$ for all $(P',R')\in D$ (problem (2)).
--
--   **Assumption 1** for a law $\nu$ on $\mathbb R$ with distribution function $F$: $F$ has a derivative $f$ everywhere, the hazard rate $r=f/(1-F)$ is differentiable with derivative $r'$, and
--   1. $2r(a)^2+r'(a)>0$ for all $a$;
--   2. $[1-F(a)]^2/r(a)\to0$ as $a\to\infty$;
--   3. $F(a)^2/r(a)\to0$ as $a\to-\infty$.
--
--   **Assumption 2** at $(P^{NV},R^{NV})$: $P^{NV}>c$, $R^{NV}-bP^{NV}>0$ and $\mathbb E[H_T(P^{NV},R^{NV})]>0$.
--
--   **Assumption 3**: $\mathbb E[(bc-A_T)^+]\le[2b(c-s)]\wedge\sqrt{4b\,\mathbb E[H_T(P^{NV},R^{NV})]}$.
--
--   These are the hypotheses of Proposition 1 and, with Assumptions 4–5, of Propositions 4–5 and Theorem 2.
--
--   **Formalization Note** The expectation is a Bochner integral; statements that use it carry or derive the integrability of the negative part of $A$. In Assumption 1 the density, hazard rate and its derivative are witnesses tied to $F$ by derivative statements, so no default value of a derivative can satisfy it. A maximizer is "a" maximizer: uniqueness is Proposition 1.
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, (2)–(3), Assumptions 1–3, p.8

import Mathlib
import Definitions.Def_HedgePSNV_Params

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace HedgePSNV

/-- The expected production payoff `E_Q[H_T(P,R)]` of the decision `(P, R)` when the market
size is the random variable `A` on `(Ω, Q)`, arXiv:2201.01026v4, (3), p.8:
`E[H_T(P,R)] = (P − c)(R − bP) − (P − s)E[(R − A_T)^+]`.

Taking `Q = P` and `A = A_T` gives the newsvendor's expected payoff; taking `Q = P^M` gives
`V_0(P,R) = E^M[H_T(P,R)]` (p.15); taking `Ω = ℝ`, `A = id` gives the value for a market-size
law `Q` on `ℝ`.

**Formalization Note** A Bochner integral; every statement using it carries (or derives) the
integrability of the negative part of `A`, so that the value is the paper's. -/
noncomputable def nvValue (p : Params) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (A : Ω → ℝ) (P R : ℝ) : ℝ :=
  ∫ ω, payoff p P R (A ω) ∂Q

/-- `(P, R)` maximizes the expected production payoff over the decision domain, problem (2),
arXiv:2201.01026v4, p.8: `(P^NV, R^NV) := arg max E[H_T(P,R)]` s.t. `P ≥ c`, `R − bP ≥ 0`.
This is "a" maximizer; uniqueness is Proposition 1 and is not built in. -/
def IsNVMaximizer (p : Params) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (A : Ω → ℝ)
    (P R : ℝ) : Prop :=
  (P, R) ∈ decisionDomain p ∧
    ∀ P' R' : ℝ, (P', R') ∈ decisionDomain p → nvValue p Q A P' R' ≤ nvValue p Q A P R

/-- Assumption 1, arXiv:2201.01026v4, p.8, for a market-size law `ν` on `ℝ` with distribution
function `F` (`cdf ν`): `F` has a derivative `f` (the density) everywhere, the hazard rate
`r = f/(1 − F)` is differentiable with derivative `r'`, `2r(a)² + r'(a) > 0` for all `a`,
`[1 − F(a)]²/r(a) → 0` as `a → ∞`, and `F(a)²/r(a) → 0` as `a → −∞`.

**Formalization Note** The density, the hazard rate and its derivative are witnesses tied to
`F` by `HasDerivAt`, so no junk `deriv` value can satisfy the condition. The paper imposes the
assumption on the law of `A_T` under `P` and under `P^M`; statements apply it to both laws. -/
def Assumption1 (ν : Measure ℝ) : Prop :=
  ∃ f r r' : ℝ → ℝ,
    (∀ a, HasDerivAt (fun x => cdf ν x) (f a) a) ∧
    (∀ a, r a = f a / (1 - cdf ν a)) ∧
    (∀ a, HasDerivAt r (r' a) a) ∧
    (∀ a, 0 < 2 * r a ^ 2 + r' a) ∧
    Tendsto (fun a => (1 - cdf ν a) ^ 2 / r a) atTop (𝓝 0) ∧
    Tendsto (fun a => cdf ν a ^ 2 / r a) atBot (𝓝 0)

/-- Assumption 2, arXiv:2201.01026v4, p.8, at the newsvendor solution `(P^NV, R^NV)`:
`P^NV > c`, `Q^NV = R^NV − bP^NV > 0` and `E[H_T(P^NV, R^NV)] > 0`. -/
def Assumption2 (p : Params) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (A : Ω → ℝ)
    (PNV RNV : ℝ) : Prop :=
  p.c < PNV ∧ 0 < RNV - p.b * PNV ∧ 0 < nvValue p Q A PNV RNV

/-- Assumption 3, arXiv:2201.01026v4, p.8:
`E[(bc − A_T)^+] ≤ [2b(c − s)] ∧ √(4b E[H_T(P^NV, R^NV)])`. -/
def Assumption3 (p : Params) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (A : Ω → ℝ)
    (PNV RNV : ℝ) : Prop :=
  ∫ ω, max (p.b * p.c - A ω) 0 ∂Q ≤
    min (2 * p.b * (p.c - p.s)) (Real.sqrt (4 * p.b * nvValue p Q A PNV RNV))

end HedgePSNV


