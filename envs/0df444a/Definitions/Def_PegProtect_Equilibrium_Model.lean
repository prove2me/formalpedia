-- Prove2me | Definitions.Def_PegProtect_Equilibrium_Model
-- name    : PegProtect_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:32:40.59986+00:00
-- url     : https://prove2.me/theorems/8c42995c-830a-4cb4-94b5-ffa291b77966
-- title:
--   §3.1–§3.5, pp. 11–17 — limit-order market with protected midpoint pegs: discrete Laplace queue, arrival operator T, surpluses πp, πm, profits πr, πs, market equilibrium
-- statement:
--   This file fixes the baseline model of Aldrich and Friedman for a single exchange on which investors choose between **midpoint peg orders**, which rest in a hidden queue at the fundamental value $V$ and are protected from sniping by a short message delay, and **market orders**, which execute immediately; proprietary traders choose between acting as **market makers** at the best bid and offer and as **snipers**.
--
--   **Parameters.** A parameter vector consists of the flow cost of speed $c$, the midpoint execution fee $d$, the investor gross surplus $\varphi$, the discount rate $\delta$ of a resting pegged order, the investor arrival rate $\rho$ on each side of the market, and the one-sided innovation rate $\nu$ of the fundamental value. The **standing restrictions** are
--   $$c>0,\qquad 0\le d<1,\qquad \varphi>1,\qquad \delta>0,\qquad \rho>0,\qquad \nu>0 .$$
--   The discount factor is $\beta=\exp(-\delta/\rho)$, so $0<\beta<1$ under the standing restrictions.
--
--   **The order imbalance.** The state $k\in\mathbb Z$ of the hidden midpoint queue counts $k$ resting sell pegs when $k>0$ and $-k$ resting buy pegs when $k<0$. If a fraction $\omega$ of investor arrivals are pegs, one arrival maps a distribution $p=(p_k)_{k\in\mathbb Z}$ to $Tp$ with
--   $$Tp_k=\begin{cases}\tfrac{\omega}{2}p_{k+1}+\tfrac{1-\omega}{2}p_k+\tfrac12 p_{k-1}, & k<0,\\[2pt] \tfrac12 p_1+(1-\omega)p_0+\tfrac12 p_{-1}, & k=0,\\[2pt] \tfrac12 p_{k+1}+\tfrac{1-\omega}{2}p_k+\tfrac{\omega}{2}p_{k-1}, & k>0,\end{cases}$$
--   and a distribution is a family $p_k\ge0$ with $\sum_{k\in\mathbb Z}p_k=1$. The **discrete Laplace law** is
--   $$q_k=\frac{1-\omega}{1+\omega}\,\omega^{|k|},\qquad k\in\mathbb Z .$$
--
--   **Payoffs.** The expected net surplus of a midpoint peg order and of a market order are
--   $$\pi_p(\omega)=(\varphi-d)\Big[\sum_{k=-\infty}^{-1}q_k+\sum_{k=0}^{\infty}q_k\beta^{k+1}\Big],\qquad \pi_m(\omega)=(\varphi-d)\sum_{k=-\infty}^{-1}q_k+(\varphi-1)\sum_{k=0}^{\infty}q_k .$$
--   With masses $N_r$ of market makers and $N_s$ of snipers (real numbers), the flow profits of a sniper and of a market maker are
--   $$\pi_s=2\nu\frac{N_r}{N_s}-c,\qquad \pi_r=\frac{2(1-\omega)\rho\sum_{k=0}^{\infty}q_k}{N_r}-2\nu .$$
--
--   **Market equilibrium** (Definition 3.1). A triple $(\omega,N_r,N_s)$ is a market equilibrium if (1) either $\omega\in(0,1)$ and $\pi_p(\omega)=\pi_m(\omega)$, or $\omega=0$ and $\pi_p(0)\le\pi_m(0)$; and (2) $N_s\ge0$, $N_r\ge0$ and $\pi_s=\pi_r=0$.
--
--   **Candidate equilibrium.** Finally
--   $$\hat\omega=\frac{\varphi-d-\beta^{-1}(\varphi-1)}{1-d},\qquad \omega^*=\max\{0,\hat\omega\},\qquad N_r^*=\frac{\rho}{\nu}\,\frac{1-\omega^*}{1+\omega^*},\qquad N_s^*=\frac{2\rho}{c}\,\frac{1-\omega^*}{1+\omega^*}.$$
--
--   These objects are the vocabulary of Propositions 3.1 and 3.2 and of every step of their proofs.
--
--   **Formalization Note** All quantities are real. The paper's Proposition 3.2 prints $\varphi\ge1$; the standing restrictions use $\varphi>1$ from Assumption A4a, because at $\varphi=1$ no market equilibrium exists. The fee restriction is the proposition's $d\ge0$ rather than A4b's $d>0$. One-sided sums are `tsum` over $\mathbb N$, with $\sum_{k=-\infty}^{-1}$ indexed by $k=-(n+1)$; `tsum` of a non-summable family is $0$, but every sum is summable for $0\le\omega<1$, the only range Definition 3.1 admits. $\omega^{|k|}$ is a natural-number power, so at $\omega=0$ the law $q$ is the point mass at $0$. The profit $\pi_r$ is written with $\sum_{k\ge0}q_k$ as in its derivation on p. 16; its closed form (3.5) is a separate statement. Division by a zero mass returns $0$ in Lean, so a zero mass gives $\pi_s=-c\ne0$ or $\pi_r=-2\nu\ne0$ and is never an equilibrium, as on the page, where the profit at zero mass is unbounded.
-- source:
--   Aldrich & Friedman, Order Protection through Delayed Messaging, SSRN 2999059 (version of March 3, 2019), pp. 11–17, §3.1 Assumptions A1–A5, §3.2 (p. 14), (3.1) p. 15, (3.2) p. 15, (3.3)–(3.5) p. 16, Definition 3.1 and (3.6)–(3.8) p. 17, (3.9) p. 18, (A.1a)–(A.1c) and the set P p. 34

import Mathlib

namespace PegProtect.Equilibrium

/-- The exogenous parameters of the baseline model (§3.1, pp. 11–12; Definition 3.1, p. 17):
`c` the flow cost of speed (A5), `d` the midpoint execution fee (A4b), `phi` the investor gross
surplus ϕ (A4a), `δ` the discount rate of a resting pegged order (A4c), `ρ` the investor arrival
rate on each side of the market (A4), `ν` the one-sided innovation rate of the fundamental value (A3). -/
structure Params where
  c : ℝ
  d : ℝ
  phi : ℝ
  δ : ℝ
  ρ : ℝ
  ν : ℝ

/-- The standing parameter restrictions of Proposition 3.2 (p. 17): `c > 0`, `1 > d ≥ 0`,
`ϕ > 1` (Assumption A4a, p. 11), `δ > 0` (A4c), `ρ, ν > 0` (A3, A4). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.c ∧ 0 ≤ P.d ∧ P.d < 1 ∧ 1 < P.phi ∧ 0 < P.δ ∧ 0 < P.ρ ∧ 0 < P.ν

/-- The discount factor `β = exp(−δ/ρ)` (p. 15). -/
noncomputable def Params.beta (P : Params) : ℝ := Real.exp (-(P.δ / P.ρ))

/-- The discrete Laplace law (3.1): `q_k = ((1 − ω)/(1 + ω)) ω^{|k|}` for `k ∈ ℤ`. -/
noncomputable def q (ω : ℝ) (k : ℤ) : ℝ := (1 - ω) / (1 + ω) * ω ^ k.natAbs

/-- The operator `T` of (A.1a)–(A.1c) (p. 34): the law of the order imbalance after one investor
arrival, when the imbalance has law `p` and an arrival is a midpoint peg order with probability `ω`. -/
noncomputable def T (ω : ℝ) (p : ℤ → ℝ) (k : ℤ) : ℝ :=
  if k < 0 then ω / 2 * p (k + 1) + (1 - ω) / 2 * p k + 1 / 2 * p (k - 1)
  else if k = 0 then 1 / 2 * p 1 + (1 - ω) * p 0 + 1 / 2 * p (-1)
  else 1 / 2 * p (k + 1) + (1 - ω) / 2 * p k + ω / 2 * p (k - 1)

/-- Membership in the set `P` of distribution functions (Appendix A, p. 34):
`p_k ≥ 0` for every `k ∈ ℤ` and `Σ_{k=−∞}^{∞} p_k = 1`. -/
def IsDistribution (p : ℤ → ℝ) : Prop := (∀ k, 0 ≤ p k) ∧ HasSum p 1

/-- The expected net surplus of a midpoint peg order, first line of (3.2) (p. 15):
`π_p = (ϕ − d) [Σ_{k=−∞}^{−1} q_k + Σ_{k=0}^{∞} q_k β^{k+1}]`. -/
noncomputable def piP (P : Params) (ω : ℝ) : ℝ :=
  (P.phi - P.d) * ((∑' n : ℕ, q ω (-((n : ℤ) + 1))) + ∑' n : ℕ, q ω n * P.beta ^ (n + 1))

/-- The expected net surplus of a market order, first expression of (3.3) (p. 16):
`π_m = (ϕ − d) Σ_{k=−∞}^{−1} q_k + (ϕ − 1) Σ_{k=0}^{∞} q_k`. -/
noncomputable def piM (P : Params) (ω : ℝ) : ℝ :=
  (P.phi - P.d) * (∑' n : ℕ, q ω (-((n : ℤ) + 1))) + (P.phi - 1) * ∑' n : ℕ, q ω n

/-- The expected flow profit of a sniper (3.4) (p. 16): `π_s = 2ν N_r/N_s − c`. -/
noncomputable def piS (P : Params) (Nr Ns : ℝ) : ℝ := 2 * P.ν * (Nr / Ns) - P.c

/-- The expected flow profit of a market maker (p. 16): market orders arrive on each side at rate
`(1 − ω)ρ` and meet no contra-side midpoint liquidity with probability `Σ_{k=0}^{∞} q_k`; a half-spread
is gained on each side and lost to snipers at rate `ν` on each side, shared by the mass `N_r`. -/
noncomputable def piR (P : Params) (ω Nr : ℝ) : ℝ :=
  2 * ((1 - ω) * P.ρ * (∑' n : ℕ, q ω n)) / Nr - 2 * P.ν

/-- Definition 3.1 (p. 17): `(ω, N_r, N_s)` is a market equilibrium if
(1) at `ω ∈ (0, 1)` a midpoint peg order has the same expected net surplus as a market order, or
`ω = 0` and it has no more; and (2) `N_s ≥ 0`, `N_r ≥ 0` and snipers and market makers earn zero
expected profit. -/
def IsMarketEquilibrium (P : Params) (ω Nr Ns : ℝ) : Prop :=
  ((0 < ω ∧ ω < 1 ∧ piP P ω = piM P ω) ∨ (ω = 0 ∧ piP P 0 ≤ piM P 0)) ∧
  0 ≤ Ns ∧ 0 ≤ Nr ∧ piS P Nr Ns = 0 ∧ piR P ω Nr = 0

/-- The last expression of (3.9) (p. 18): `(ϕ − d − β^{−1}(ϕ − 1))/(1 − d)`. -/
noncomputable def omegaHat (P : Params) : ℝ :=
  (P.phi - P.d - P.beta⁻¹ * (P.phi - 1)) / (1 - P.d)

/-- (3.6) (p. 17): `ω* = max{0, (ϕ − d − β^{−1}(ϕ − 1))/(1 − d)}`. -/
noncomputable def omegaStar (P : Params) : ℝ :=
  max 0 ((P.phi - P.d - P.beta⁻¹ * (P.phi - 1)) / (1 - P.d))

/-- (3.7) (p. 17): `N*_r = (ρ/ν)((1 − ω*)/(1 + ω*))`. -/
noncomputable def NrStar (P : Params) : ℝ :=
  P.ρ / P.ν * ((1 - omegaStar P) / (1 + omegaStar P))

/-- (3.8) (p. 17): `N*_s = (2ρ/c)((1 − ω*)/(1 + ω*))`. -/
noncomputable def NsStar (P : Params) : ℝ :=
  2 * P.ρ / P.c * ((1 - omegaStar P) / (1 + omegaStar P))

end PegProtect.Equilibrium


