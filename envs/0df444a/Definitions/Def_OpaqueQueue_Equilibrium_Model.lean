-- Prove2me | Definitions.Def_OpaqueQueue_Equilibrium_Model
-- name    : OpaqueQueue_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:21.440518+00:00
-- url     : https://prove2.me/theorems/5b7168ef-d5b2-4cca-8c2b-0f8da4ee2f90
-- title:
--   §3–§3.2, pp. 8–15 — M/M/1 queue with rationally inattentive customers: payoff (1), problem (9), GMNL joining probabilities (14), stationary law (21), equilibrium (Definition 1)
-- statement:
--   This file fixes the model of Canyakmaz and Boyacı: a single-server first-come-first-served queue whose arriving customers cannot see the queue length and decide whether to join after acquiring costly information.
--
--   1. **Parameters and standing assumptions.** Customers arrive as a Poisson process with rate $\lambda>0$; service times are exponential with mean $1/\mu$, $\mu>0$. A served customer receives the reward $R$ and pays the price $p$; waiting costs $C>0$ per unit of time; processing information costs $\theta>0$ per nat of mutual information. It is assumed that $R>p$. The **utilization factor** is $\rho=\lambda/\mu$.
--   2. **Payoff (1).** A customer who finds $n$ customers in the system and joins obtains
--   $$v_n = R - p - \frac{C}{\mu}\,n .$$
--   3. **Joining probabilities (8)/(14).** If $q\in[0,1]$ is the unconditional probability of joining, the probability of joining in state $n$ is given by the generalized multinomial logit formula
--   $$\pi_n(q) = \frac{q\,e^{v_n/\theta}}{1-q+q\,e^{v_n/\theta}} .$$
--   4. **Stationary law (21).** With state-dependent arrival rates $\lambda_n=\lambda\pi_n(q)$, put $a_0=1$ and $a_k = \lambda_0\lambda_1\cdots\lambda_{k-1}/\mu^k = \rho^k\pi_0(q)\cdots\pi_{k-1}(q)$. The value $q$ is **admissible** if $q\in[0,1]$ and $\sum_k a_k<\infty$; then the steady-state law of the number of customers is
--   $$g_n(q) = \frac{a_n}{\sum_{k\ge 0} a_k},\qquad\text{so } g_0(q) = \Big(1+\sum_{k\ge1}a_k\Big)^{-1},\; g_n(q) = g_0(q)\,\rho^n\pi_0(q)\cdots\pi_{n-1}(q).$$
--   5. **The customer's problem (9).** For a prior $g$ on the number of customers in the system, the customer chooses the unconditional joining probability $x\in[0,1]$ to maximize
--   $$f(x; g) = \theta\sum_{n\ge0} g_n \log\big(x\,e^{v_n/\theta}+1-x\big)$$
--   (natural logarithm). With $g=g(q)$ this is the function $f(x;q)$ of (24).
--   6. **Equilibrium (Definition 1).** A number $\tilde\pi$ is an equilibrium unconditional joining probability if it is admissible, satisfies the consistency equation (15) $\tilde\pi=\sum_n\tilde\pi_n\,\tilde g(n)$ with $\tilde\pi_n=\pi_n(\tilde\pi)$ and $\tilde g=g(\tilde\pi)$, and solves the customer's problem (9) under the prior $\tilde g$.
--   7. **The function (25).** $\varphi_n(x;\theta) = (e^{v_n/\theta}-1)/(x e^{v_n/\theta}+1-x)$, so that $\partial f/\partial x = \theta\sum_n g_n\varphi_n$.
--
--   These objects are shared by every statement of the mission: Theorem 1 asserts that exactly one equilibrium exists.
--
--   **Formalization Note** All quantities are real; states are natural numbers. Clause 6's optimality requirement is the reading of "equilibrium" in Definition 1: equations (14)–(15) alone are necessary conditions only (the paper says so for (8) on p. 13), and without optimality $q=0$ would always satisfy them, and $q=1$ would whenever $\lambda<\mu$. The proof of Theorem 1 uses exactly this best response (its (23)). The law $g(q)$ is defined as $a_n/\sum_k a_k$ for every $q$, but it is a probability vector only for admissible $q$ (Lean's sum of a divergent series is $0$), so every statement about it assumes admissibility. The positivity of $C$, $\lambda$, $\mu$ is implicit in the paper and is stated explicitly.
-- source:
--   Canyakmaz & Boyacı, Opaque Queues: Service Systems with Rationally Inattentive Customers, ESMT Working Paper 18-04 (September 24, 2018), pp. 8–15 (PDF 9–16), §3, §3.1, §3.2, eqs. (1), (5), (8), (9), (14), (15), Definition 1; Appendix pp. 33–34 (PDF 34–35), eqs. (21), (23)–(25)

import Mathlib

namespace OpaqueQueue.Equilibrium

/-- Parameters of the single-server FCFS queue of §3, pp. 8–9: Poisson arrival rate `lam` (λ),
exponential service with mean `1 / mu` (µ the service rate), reward `R`, price `p`, delay cost `C`
per unit of waiting time, and information cost `θ` (Definition 1). -/
structure Params where
  lam : ℝ
  mu : ℝ
  R : ℝ
  p : ℝ
  C : ℝ
  θ : ℝ

/-- Standing assumptions of §3 and Definition 1: λ > 0 and µ > 0 (Poisson arrivals, exponential
service, pp. 8–9), C > 0 (a delay cost of C per time unit, p. 9; made explicit), R > p (p. 9:
"Let us assume that R > p so that v0 > 0"), and θ > 0 (Definition 1). No sign is assumed on p. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.lam ∧ 0 < P.mu ∧ 0 < P.C ∧ P.p < P.R ∧ 0 < P.θ

/-- The utilization factor ρ = λ/µ (p. 14). -/
noncomputable def rho (P : Params) : ℝ := P.lam / P.mu

/-- The payoff (1), p. 9: `v n = R − p − (C/µ) n` for a customer who finds `n` customers in the
system. -/
noncomputable def v (P : Params) (n : ℕ) : ℝ := P.R - P.p - P.C / P.mu * n

/-- The conditional joining probability in state `n` when the unconditional joining probability is
`q`: `πn(q) = q e^{vn/θ} / (1 − q + q e^{vn/θ})`, the GMNL formula (8), p. 12, written as in (14),
p. 14, and (21), p. 33. -/
noncomputable def joinProb (P : Params) (q : ℝ) (n : ℕ) : ℝ :=
  q * Real.exp (v P n / P.θ) / (1 - q + q * Real.exp (v P n / P.θ))

/-- The unnormalized stationary weights `a k = ρ^k π0(q) π1(q) ⋯ π_{k−1}(q)`, with `a 0 = 1`.
With state-dependent arrival rates `λn = λ πn(q)` (Definition 1, p. 15) this is
`λ0 λ1 ⋯ λ_{k−1} / µ^k`, the product of Definition 1 and of (21), p. 33. -/
noncomputable def weight (P : Params) (q : ℝ) (k : ℕ) : ℝ :=
  rho P ^ k * ∏ i ∈ Finset.range k, joinProb P q i

/-- `q` is admissible: it is a probability and the stationary series `Σ_k a k` converges, i.e.
"the queue distribution in steady-state is well-defined" (proof of Theorem 1, p. 33). -/
def Admissible (P : Params) (q : ℝ) : Prop :=
  q ∈ Set.Icc (0 : ℝ) 1 ∧ Summable (weight P q)

/-- The stationary law (21), p. 33, of the birth–death queue with arrival rates `λ πn(q)` and
service rate µ: `gn(q) = a n / Σ_k a k`. Since `a 0 = 1`, `g0(q) = (1 + Σ_{k≥1} a k)^{-1}` and
`gn(q) = g0(q) ρ^n π0(q) ⋯ π_{n−1}(q)`, exactly the `g̃0`, `g̃n` of Definition 1, p. 15, at
`q = π̃`. It is a probability vector only when `q` is `Admissible` (otherwise Lean's `tsum` of a
non-summable series is `0` and the value is junk); every statement about it assumes admissibility. -/
noncomputable def stat (P : Params) (q : ℝ) (n : ℕ) : ℝ :=
  weight P q n / ∑' k, weight P q k

/-- The customer's objective in (9), p. 12, for a prior `g` on the number of customers in the
system: `θ Σn gn log(x e^{vn/θ} + 1 − x)` (natural logarithm). With `g = stat P q` it is the
`f(x; q)` of (24), p. 34. -/
noncomputable def obj (P : Params) (g : ℕ → ℝ) (x : ℝ) : ℝ :=
  P.θ * ∑' n, g n * Real.log (x * Real.exp (v P n / P.θ) + 1 - x)

/-- `x` solves problem (9), `max_{π̄ ∈ [0,1]} θ E_G[log(π̄ e^{vn/θ} + 1 − π̄)]`, under the prior
`g`. -/
def IsOptimal (P : Params) (g : ℕ → ℝ) (x : ℝ) : Prop :=
  x ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ y ∈ Set.Icc (0 : ℝ) 1, obj P g y ≤ obj P g x

/-- The equilibrium of Definition 1, p. 14–15, with unconditional joining probability `q = π̃`:
1. `q ∈ [0,1]` and the stationary law `g̃ = stat P q` is well-defined (`Admissible`);
2. consistency (15): `π̃ = Σn π̃n g̃(n)` with `π̃n = joinProb P q n` from (14);
3. `q` solves the customer's problem (9) under the equilibrium prior `g̃` (the best response
   (23) of the proof of Theorem 1, p. 34).
Clause 3 is the reading of "equilibrium": (14)–(15) alone are necessary conditions only, which
the paper itself notes on p. 13 for (8); without clause 3, `q = 0` would always satisfy clauses
1–2, and `q = 1` would whenever λ < µ. The conditional probabilities `π̃n` and the law `g̃` are
functions of `q`, so `q` determines the whole equilibrium. -/
def IsEquilibrium (P : Params) (q : ℝ) : Prop :=
  Admissible P q ∧ q = ∑' n, joinProb P q n * stat P q n ∧ IsOptimal P (stat P q) q

/-- `φn(x; θ) = (e^{vn/θ} − 1) / (x e^{vn/θ} + 1 − x)` of (25), p. 34, so that
`∂f/∂x (x; q) = θ Σn gn(q) φn(x; θ)`. -/
noncomputable def phi (P : Params) (x : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (v P n / P.θ) - 1) / (x * Real.exp (v P n / P.θ) + 1 - x)

end OpaqueQueue.Equilibrium


