-- Prove2me | Definitions.Def_LindleyQueue_Stability_Model
-- name    : LindleyQueue_Stability_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:18:42.660986+00:00
-- url     : https://prove2.me/theorems/5eb487cf-1694-48d8-8815-1e164ac89d02
-- title:
--   Assumptions 1–2 and recursion (1): interarrival and service times, $u_r = s_r - t_r$, waiting times $w_r$, $F_r(x)$, $U_n$, $G$ and the limit $F(x)$
-- statement:
--   This file fixes the single-server queue of Lindley (1952), §§2–4.
--
--   **The input (Assumptions 1 and 2).** Customers arrive in order at a single server. On a probability space $(\Omega, \mathcal F, P)$ let $t_r$ be the time between the arrivals of the $r$th and the $(r+1)$th customer and $s_r$ the service time of the $r$th customer. It is assumed that
--
--   1. the $t_r$ are independent, identically distributed, and $\mathscr{E}(t_r)$ is finite (Assumption 1);
--   2. the $s_r$ are independent, identically distributed, and $\mathscr{E}(s_r)$ is finite (Assumption 2);
--   3. the two families $\{s_r\}$ and $\{t_r\}$ are independent of each other (Assumption 2);
--   4. every $s_r$ and every $t_r$ is a nonnegative measurable random variable (they are times; simultaneous arrivals, $t_r = 0$, are allowed).
--
--   **Derived quantities.** Put $u_r = s_r - t_r$. The waiting times obey Lindley's recursion (1):
--
--   $$
--   w_1 = 0, \qquad w_{r+1} = \begin{cases} w_r + u_r & \text{if } w_r + u_r > 0,\\ 0 & \text{if } w_r + u_r \le 0,\end{cases}
--   $$
--
--   that is, $w_{r+1} = \max(w_r + u_r, 0)$. Further:
--
--   - $F_r(x) = p(w_r \le x)$ is the distribution function of the waiting time of the $r$th customer;
--   - $U_n = u_1 + \dots + u_n$ is the associated random walk ($U_0 = 0$);
--   - $G$ is the law of $u_1$ (its distribution function is the paper's d.f. $G$);
--   - the limit function is $F(x) = p(U_s \le x \text{ for all } s \ge 1)$ for $x \ge 0$ and $F(x) = 0$ for $x < 0$.
--
--   These are the objects in which Lindley's stability theorem and its supporting identities (3), (4), cases (i)–(iii) are stated.
--
--   **Formalization Note** Customers are numbered from $0$ in Lean: `w 0` is the paper's $w_1$, `w r` is $w_{r+1}$, `F r x` is $F_{r+1}(x)$, `s r`, `t r`, `u r` are $s_{r+1}, t_{r+1}, u_{r+1}$, and `U n` $= \sum_{i<n}$ `u i` is the paper's $U_n$. Independence of the two families is independence of the random sequences $(s_r)_r$ and $(t_r)_r$ as random elements of $\mathbb R^{\mathbb N}$. Nonnegativity of $s_r, t_r$ is added explicitly (the paper calls them positive times, p. 279); no statement depends on it. The probability measure $P$ is a parameter; theorems assume `IsProbabilityMeasure P`. `G` is the push-forward measure `P.map (u 0)`, and Stieltjes integrals $\int \cdots dG(u)$ become Lebesgue integrals against it. `Flim` is the paper's $F(x)$, with the case split $x \ge 0$ / $x < 0$ built in.
-- source:
--   Lindley (Proc. Camb. Phil. Soc. 48, 1952), §2, Assumptions 1–2 and eq. (1), pp. 277–278; §3, U_r, p. 279; limit F(x), p. 280

import Mathlib

namespace LindleyQueue.Stability

open MeasureTheory ProbabilityTheory

/-- The input of Lindley's single-server queue (Lindley 1952, §2, Assumptions 1 and 2,
pp. 277–278). Customers are numbered from `0` (the paper numbers them from `1`):
`t r` is the time between the arrivals of customers `r` and `r + 1`, and `s r` is the service
time of customer `r`.

* Assumption 1: the `t r` are independent, identically distributed, with finite mean.
* Assumption 2: the `s r` are independent, identically distributed, with finite mean, and the
  two families `{s r}` and `{t r}` are independent of each other.
* Service and interarrival times are times, hence nonnegative (the paper calls them positive,
  p. 279, and allows simultaneous arrivals, p. 277, so `t r = 0` is allowed). -/
structure Input (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- Service time of customer `r` (the paper's `s_{r+1}`). -/
  s : ℕ → Ω → ℝ
  /-- Time between the arrivals of customers `r` and `r + 1` (the paper's `t_{r+1}`). -/
  t : ℕ → Ω → ℝ
  measurable_s : ∀ r, Measurable (s r)
  measurable_t : ∀ r, Measurable (t r)
  /-- Assumption 2: the service times are independent. -/
  iIndepFun_s : iIndepFun s P
  /-- Assumption 1: the interarrival times are independent. -/
  iIndepFun_t : iIndepFun t P
  /-- Assumption 2: the service times are identically distributed. -/
  identDistrib_s : ∀ r, IdentDistrib (s r) (s 0) P P
  /-- Assumption 1: the interarrival times are identically distributed. -/
  identDistrib_t : ∀ r, IdentDistrib (t r) (t 0) P P
  /-- Assumption 2: `𝓔(s_r)` is finite. -/
  integrable_s : Integrable (s 0) P
  /-- Assumption 1: `𝓔(t_r)` is finite. -/
  integrable_t : Integrable (t 0) P
  /-- Assumption 2: the families `{s_r}` and `{t_r}` are independent. -/
  indepFun_s_t : IndepFun (fun ω r => s r ω) (fun ω r => t r ω) P
  nonneg_s : ∀ r ω, 0 ≤ s r ω
  nonneg_t : ∀ r ω, 0 ≤ t r ω

namespace Input

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `u r = s r - t r`, the paper's `u_{r+1} = s_{r+1} - t_{r+1}` (p. 278). -/
def u (Q : Input Ω P) (r : ℕ) (ω : Ω) : ℝ :=
  Q.s r ω - Q.t r ω

/-- The waiting times, by recursion (1) (p. 278): `w 0 = 0` (the paper's `w_1 = 0`) and
`w (r + 1) = w r + u r` if this is positive, `0` otherwise. `w r` is the paper's `w_{r+1}`. -/
def w (Q : Input Ω P) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | r + 1 => fun ω => max (Q.w r ω + Q.u r ω) 0

/-- `F r x = p(w r ≤ x)`, the distribution function of the waiting time of customer `r`
(the paper's `F_{r+1}(x)`, p. 278), right-continuous by definition. -/
noncomputable def F (Q : Input Ω P) (r : ℕ) (x : ℝ) : ℝ :=
  P.real {ω | Q.w r ω ≤ x}

/-- The random walk `U n = u 0 + ⋯ + u (n - 1)`, the paper's `U_n = u_1 + ⋯ + u_n` (p. 279);
`U 0 = 0` is the empty sum. -/
def U (Q : Input Ω P) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, Q.u i ω

/-- `G`, the law (distribution) of `u`; the paper's d.f. `G` (p. 278) is its distribution
function. All `u r` have this law. -/
noncomputable def G (Q : Input Ω P) : Measure ℝ :=
  P.map (Q.u 0)

/-- The limit function `F(x)` of p. 280: `F(x) = p(U_n ≤ x for all n ≥ 1)` for `x ≥ 0`, and
`F(x) = 0` for `x < 0`. -/
noncomputable def Flim (Q : Input Ω P) (x : ℝ) : ℝ :=
  if 0 ≤ x then P.real {ω | ∀ n : ℕ, 1 ≤ n → Q.U n ω ≤ x} else 0

end Input

end LindleyQueue.Stability


