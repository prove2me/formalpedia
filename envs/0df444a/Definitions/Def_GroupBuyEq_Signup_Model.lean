-- Prove2me | Definitions.Def_GroupBuyEq_Signup_Model
-- name    : GroupBuyEq_Signup_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:52.974076+00:00
-- url     : https://prove2.me/theorems/7b44426b-64f9-4cfc-87f4-ade50f0dd8f1
-- title:
--   §3.1–§3.2, pp. 6–10 — two-threshold group-buying event: prices, sign-up value V_k (1), threshold ū (3), sign-up probability H_k (2), dynamic consumer equilibrium (4)–(5)
-- statement:
--   This file fixes the objects of the two-threshold group-buying model of Ming and Tunca, on which the existence and uniqueness of the dynamic consumer equilibrium is stated.
--
--   **Parameters.** A group-buying event runs on the time window $[0,T]$, during which customers arrive according to a Poisson process with rate $\lambda_g$. A customer who signs up pays a non-refundable deposit $d$. There are two sign-up thresholds $M_1\le M_2$ (natural numbers), a base price $p_0$ and a constant deal discount $\delta$, which determine the two deal prices
--   $$p_1=p_0-\delta,\qquad p_2=p_1-\delta .$$
--   If the final number $N$ of sign-ups satisfies $N<M_1$ the price is $p_0$, if $M_1\le N<M_2$ it is $p_1$, and if $N\ge M_2$ it is $p_2$. The **standing assumptions** are
--   $$T>0,\quad \lambda_g>0,\quad 0<M_1\le M_2,\quad d>0,\quad 0<\delta<p_0/2,\quad d\le p_2 .$$
--
--   **Value of signing up** (1). After the event a customer with reservation utility $u$ who signed up pays the balance if $u-p\ge -d$ and walks away otherwise, so his surplus is $\max\{u-p,-d\}$. If $a$ and $b$ are the probabilities that only the first deal, resp. the second deal, happens once he has joined, his expected utility of signing up is
--   $$V(a,b,u)=a\max\{u-p_1,-d\}+b\max\{u-p_2,-d\}+(1-a-b)\max\{u-p_0,-d\}.$$
--
--   **Threshold** (3). With the same $a,b$,
--   $$\bar u(a,b)=\begin{cases} p_0-2\delta-d\left(1-\frac1b\right) & \text{if } 0\le d\le \delta b,\\[2pt] p_0-d+\frac{d-\delta(a+2b)}{a+b} & \text{if } \delta b<d\le \delta a+2\delta b,\\[2pt] p_0-\delta(a+2b) & \text{if } d>\delta a+2\delta b.\end{cases}$$
--
--   **Beliefs and sign-up probability** (2). A belief profile consists of functions $\pi^1_k(t)$, $\pi^2_k(t)$, $k\ge0$, $t\in\mathbb R$: the time-$t$ probabilities that only the first deal, resp. the second deal, happens given $N^+_t=k$ sign-ups on $[0,t]$. Given the law $\mu$ of the reservation utility, the probability that a customer arriving at $t$ who sees $N_t=k$ signs up is
--   $$H_k(t)=\mu\{u:\ V(\pi^1_{k+1}(t),\pi^2_{k+1}(t),u)\ge0\}.$$
--
--   **Dynamic consumer equilibrium.** A profile is an equilibrium when, for all $t\in[0,T]$:
--   1. every $\pi^i_k$ is measurable and $\pi^i_k(t)\in[0,1]$;
--   2. (iii) $\pi^1_k(t)=0$ and $\pi^2_k(t)=1$ for $k\ge M_2$;
--   3. (ii) $\pi^1_k(t)=1-\pi^2_k(t)$ for $M_1\le k<M_2$;
--   4. (4) for $k<M_2$,
--   $$\pi^2_k(t)=\int_0^{T-t}\big(H_k(t+x)\pi^2_{k+1}(t+x)+(1-H_k(t+x))\pi^2_k(t+x)\big)\lambda_g e^{-\lambda_g x}\,dx;$$
--   5. (5) for $k<M_1$, the same equation with $\pi^1$ in place of $\pi^2$.
--
--   These are the objects of Proposition 1 and its supporting results (Lemma 1, the boundary conditions, and the recursion (6)).
--
--   **Formalization Note** The parameters form a structure `Params`; $p_1,p_2$ are derived, not free. $0<T$ and $0<\lambda_g$ are not printed but implicit (a time window, a Poisson rate). $\mu$ is a measure on $\mathbb R$; the theorems assume it is a probability measure without atoms. The equilibrium is the solution of the paper's conditioning equations (2), (4), (5) with boundary conditions (ii)–(iii), as on p. 10; the Poisson process itself is not modelled. Equation (4) is imposed only for $k<M_2$ and (5) only for $k<M_1$, the ranges where the conditioning argument applies; the boundary condition (i) follows from them. Measurability and the $[0,1]$ range make the integrals genuine. $\pi^1+\pi^2\le1$ is not imposed: it follows. $H_k$ is defined by (2), not by the closed form (7), and the equilibrium is not defined by (6); both are theorems. In (3) Lean's $x/0=0$ is never reached on the probability simplex when $d>0$.
-- source:
--   Ming & Tunca, Consumer Equilibrium, Demand Effects, and Efficiency in Group Buying, SSRN 3352047 (version of 2020-05-15), pp. 6–10 (PDF 7–11), §3.1 Model Description and §3.2, (1)–(5), boundary conditions (ii)–(iii)

import Mathlib

namespace GroupBuyEq.Signup

/-- Primitives of the two-threshold group-buying event (§3.1, pp. 6–7): window length `T`,
Poisson arrival rate `lam` (the paper's `λg(w)`), sign-up thresholds `M1`, `M2`, base price `p0`,
deal discount `δ` and deposit `d`. -/
structure Params where
  T : ℝ
  lam : ℝ
  M1 : ℕ
  M2 : ℕ
  p0 : ℝ
  δ : ℝ
  d : ℝ

/-- First deal price, `p1 = p0 - δ` (p. 7). -/
def Params.p1 (P : Params) : ℝ := P.p0 - P.δ

/-- Second deal price, `p2 = p1 - δ` (p. 7). -/
def Params.p2 (P : Params) : ℝ := P.p1 - P.δ

/-- Standing assumptions of §3.1 and Proposition 1: `0 < T`, `0 < lam` (added: a nondegenerate
window and a Poisson rate), `0 < M1 ≤ M2`, `d > 0`, `0 < δ < p0 / 2`, `d ≤ p2`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.T ∧ 0 < P.lam ∧ 0 < P.M1 ∧ P.M1 ≤ P.M2 ∧ 0 < P.d ∧
    0 < P.δ ∧ P.δ < P.p0 / 2 ∧ P.d ≤ P.p2

/-- The expected utility (1) of signing up for a customer with reservation utility `u`, when the
probabilities that only the first deal, resp. the second deal, happens after he joins are
`a = π¹_{k+1}(t)` and `b = π²_{k+1}(t)`. -/
def V (P : Params) (a b u : ℝ) : ℝ :=
  a * max (u - P.p1) (-P.d) + b * max (u - P.p2) (-P.d) + (1 - a - b) * max (u - P.p0) (-P.d)

/-- The sign-up threshold `ū` of (3), with `a = π¹_{k+1}(t)`, `b = π²_{k+1}(t)`; the branch
conditions are exactly those printed in (3). -/
noncomputable def ubar (P : Params) (a b : ℝ) : ℝ :=
  if 0 ≤ P.d ∧ P.d ≤ P.δ * b then P.p0 - 2 * P.δ - P.d * (1 - 1 / b)
  else if P.δ * b < P.d ∧ P.d ≤ P.δ * a + 2 * P.δ * b then
    P.p0 - P.d + (P.d - P.δ * (a + 2 * b)) / (a + b)
  else P.p0 - P.δ * (a + 2 * b)

/-- A belief profile: `pi1 k t = π¹_k(t)` and `pi2 k t = π²_k(t)`, the time-`t` probabilities that
only the first deal, resp. the second deal, happens given `N⁺_t = k` sign-ups on `[0, t]`. -/
structure Profile where
  pi1 : ℕ → ℝ → ℝ
  pi2 : ℕ → ℝ → ℝ

/-- (2): the sign-up probability `H_k(t) = Pr{V_k(u, t) ≥ 0}` of a customer arriving at time `t`
who sees `N_t = k`, the reservation utility `u` having law `μ`. -/
noncomputable def H (P : Params) (μ : MeasureTheory.Measure ℝ) (E : Profile) (k : ℕ) (t : ℝ) : ℝ :=
  (μ {u | 0 ≤ V P (E.pi1 (k + 1) t) (E.pi2 (k + 1) t) u}).toReal

/-- A dynamic consumer equilibrium (§3.2, pp. 8–10): the beliefs are measurable and take values in
`[0, 1]` on `[0, T]`, satisfy the boundary conditions (iii) for `k ≥ M2` and (ii) for
`M1 ≤ k < M2`, the conditioning equation (4) for `k < M2` and (5) for `k < M1`, all for
`t ∈ [0, T]`, with the sign-up probability `H` of (2). -/
def IsEquilibrium (P : Params) (μ : MeasureTheory.Measure ℝ) (E : Profile) : Prop :=
  (∀ k, Measurable (E.pi1 k) ∧ Measurable (E.pi2 k)) ∧
  (∀ k, ∀ t ∈ Set.Icc 0 P.T, E.pi1 k t ∈ Set.Icc (0 : ℝ) 1 ∧ E.pi2 k t ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ k, P.M2 ≤ k → ∀ t ∈ Set.Icc 0 P.T, E.pi1 k t = 0 ∧ E.pi2 k t = 1) ∧
  (∀ k, P.M1 ≤ k → k < P.M2 → ∀ t ∈ Set.Icc 0 P.T, E.pi1 k t = 1 - E.pi2 k t) ∧
  (∀ k, k < P.M2 → ∀ t ∈ Set.Icc 0 P.T, E.pi2 k t =
      ∫ x in (0 : ℝ)..(P.T - t), (H P μ E k (t + x) * E.pi2 (k + 1) (t + x)
        + (1 - H P μ E k (t + x)) * E.pi2 k (t + x)) * P.lam * Real.exp (-(P.lam * x))) ∧
  (∀ k, k < P.M1 → ∀ t ∈ Set.Icc 0 P.T, E.pi1 k t =
      ∫ x in (0 : ℝ)..(P.T - t), (H P μ E k (t + x) * E.pi1 (k + 1) (t + x)
        + (1 - H P μ E k (t + x)) * E.pi1 k (t + x)) * P.lam * Real.exp (-(P.lam * x)))

end GroupBuyEq.Signup


