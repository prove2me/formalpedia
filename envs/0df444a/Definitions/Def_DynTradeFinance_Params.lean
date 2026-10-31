-- Prove2me | Definitions.Def_DynTradeFinance_Params
-- name    : DynTradeFinance_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:31.963282+00:00
-- url     : https://prove2.me/theorems/fe7bc57e-b744-4f45-baab-291e9d3bc901
-- title:
--   Parameters $(p_1,p_2,l_1,l_2,c,w,\mu,\lambda,\delta)$, standing assumptions and the frictionless value $\Pi_0$ (1) (corrected: $\delta<\min(\mu,1)$)
-- statement:
--   A seller borrows a principal $c$ from a bank to finance an order that goes through a two-step trade process. The model of Lee, Tang, Yang and Zhang has the parameters
--
--   1. $p_1$, the probability that the order passes Step 1, and $p_2$, the probability that it passes Step 2 given that it passed Step 1;
--   2. $l_1$ and $l_2$, the liquidation values the bank collects if the order fails Step 1, respectively Step 2;
--   3. $c$, the loan principal (the seller's production cost), and $w$, the wholesale price the buyer pays on success;
--   4. $\mu$, the rate of the exponential Step-2 duration (the Step-1 rate is normalized to $1$), and $\lambda$, the rate of the exponential information-verification delay;
--   5. $\delta$, the bank's instantaneous cost of core capital.
--
--   The risk-free rate is normalized to zero. The **standing assumptions** of §§3–4 are
--   $$0<p_1<1,\quad 0<p_2<1,\quad l_1<l_2<c<w,\quad c>0,\quad \mu>0,\quad \lambda>\mu,\quad 0<\delta<\min(\mu,1).$$
--   The **frictionless value of the order**, Eq. (1), is
--   $$\Pi_0=p_1p_2w+(1-p_1)l_1+p_1(1-p_2)l_2-c .$$
--
--   These parameters and assumptions are shared by every statement of the mission.
--
--   **Formalization Note** The paper assumes $\delta\le\min(\mu,1)$ (p. 11); at equality the expected financing cost is infinite and the paper's closed forms divide by zero, so the strict inequality is used. The positivity of the principal $c$ is implicit in the paper. The assumptions $\pi_0<\Pi_0$ and "$w$ sufficiently high" (p. 9) enter no formula and are not part of the predicate. $\lambda$ is the Lean field `lam`.
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), §3, pp. 7–9 (Eq. (1), p. 9), and §4, p. 11

import Mathlib

namespace DynTradeFinance

/-- **Parameters of the trade-finance model** of Lee, Tang, Yang, Zhang, *Dynamic trade finance
in the presence of information frictions and FinTech*, SSRN 3632563 (Feb. 2022 revision), §3,
pp. 7–9, and §4, p. 11.

* `p₁` — probability that the order passes Step 1; `p₂` — probability that it passes Step 2
  given that it passed Step 1;
* `l₁`, `l₂` — liquidation values the bank collects if the order fails Step 1, resp. Step 2;
* `c` — the loan principal (the seller borrows `c`, its production cost);
* `w` — the wholesale price the buyer pays on successful completion;
* `μ` — the rate of the Step-2 duration `T̃₂ ∼ Exp(μ)` (the Step-1 rate is normalized to 1);
* `lam` — the rate `λ` of the information delay `d̃ ∼ Exp(λ)`;
* `δ` — the bank's instantaneous cost of core capital.

The risk-free rate is normalized to zero (p. 7). -/
structure Params where
  p₁ : ℝ
  p₂ : ℝ
  l₁ : ℝ
  l₂ : ℝ
  c : ℝ
  w : ℝ
  μ : ℝ
  lam : ℝ
  δ : ℝ

/-- **Standing assumptions** of §§3–4 (SSRN 3632563, pp. 7–11): `p₁, p₂ ∈ (0,1)`;
`l₁ < l₂ < c < w` (p. 8); a positive loan principal `c > 0` (p. 7, "needs to borrow c");
`μ > 0` (p. 8); `λ > μ` (p. 9); `0 < δ` and `δ < min(μ, 1)` (p. 11).

**Formalization Note.** The paper prints `δ ≤ min(μ,1)` (p. 11). At `δ = μ` or `δ = 1` the
expected cost of capital is infinite (footnote 15: the assumption "ensures that the total expected
financing cost is finite") and the closed forms (7), (9), (10) divide by zero, so the strict
inequality is used. The positivity of the principal `c` is implicit in the paper (a loan). The
assumptions `π₀ < Π₀` and "w sufficiently high" (p. 9) enter no formula and are not included. -/
def Params.Admissible (θ : Params) : Prop :=
  0 < θ.p₁ ∧ θ.p₁ < 1 ∧ 0 < θ.p₂ ∧ θ.p₂ < 1 ∧
  θ.l₁ < θ.l₂ ∧ θ.l₂ < θ.c ∧ θ.c < θ.w ∧ 0 < θ.c ∧
  0 < θ.μ ∧ θ.μ < θ.lam ∧
  0 < θ.δ ∧ θ.δ < θ.μ ∧ θ.δ < 1

/-- **Frictionless value of the order, Eq. (1)**, SSRN 3632563, p. 9:
`Π₀ = p₁p₂w + (1 − p₁)l₁ + p₁(1 − p₂)l₂ − c`. -/
def Params.Pi0 (θ : Params) : ℝ :=
  θ.p₁ * θ.p₂ * θ.w + (1 - θ.p₁) * θ.l₁ + θ.p₁ * (1 - θ.p₂) * θ.l₂ - θ.c

end DynTradeFinance


