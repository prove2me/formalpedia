-- Prove2me | Definitions.Def_QueueBandit_QUCB_Model
-- name    : QueueBandit_QUCB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:37:53.187647+00:00
-- url     : https://prove2.me/theorems/6f122146-f2b5-42b9-8f92-faac24cd3dee
-- title:
--   §3.2, pp. 6–8 — U×K switch with Bernoulli arrivals and services, the stationary initial law, the genie queue Q* and the explore coin E(t)
-- statement:
--   This module fixes the stochastic switch of Krishnasamy, Sen, Johari and Shakkottai (§3.2) on one probability space.
--
--   There are $U$ queues and $K$ servers, indexed by $u\in[U]$ and $k\in[K]$. A **problem instance** consists of arrival probabilities $\lambda_u\in[0,1]$ and service probabilities $\mu_{uk}\in[0,1]$, together with a map $k^*:[U]\to[K]$ such that
--
--   1. (Assumption 1) $\mu_{uk}<\mu_{uk^*_u}$ for every $k\neq k^*_u$, and $k^*_u\neq k^*_{u'}$ for $u\neq u'$;
--   2. (Assumption 2) $\lambda_u<\mu^*_u$ for every $u$, where $\mu^*_u=\mu_{uk^*_u}=\max_k\mu_{uk}$.
--
--   The derived quantities are $\epsilon_u=\mu^*_u-\lambda_u$, the gap $\Delta=\min_{u,\,k\neq k^*_u}(\mu^*_u-\mu_{uk})$ and the ratio
--   $$\rho_u=\frac{\lambda_u(1-\mu^*_u)}{(1-\lambda_u)\mu^*_u}\in[0,1).$$
--   A **matching** is an injective map $\kappa:[U]\to[K]$ (queue $u$ is served by server $\kappa_u$).
--
--   The randomness of slot $t\ge1$ consists of independent uniforms $W_u(t)$ (arrivals), $V_{uk}(t)$ (links), a uniform coin $\xi_t$ and an index $J_t$ uniform on $[K]$; the slots are i.i.d. The arrivals and potential services are
--   $$A_u(t)=\mathbb 1\{W_u(t)\le\lambda_u\},\qquad R_{uk}(t)=\mathbb 1\{V_{uk}(t)\le\mu_{uk}\},$$
--   so they are independent Bernoulli$(\lambda_u)$ and Bernoulli$(\mu_{uk})$ variables, i.i.d. over slots. The **explore indicator** of Algorithm 1 is
--   $$\mathsf E(t)=\mathbb 1\Big\{\xi_t<\min\Big\{1,\;3K\frac{\log^2 t}{t}\Big\}\Big\}.$$
--   The initial state $Q(0)$ is independent of the slots and has law $\pi_{(\lambda,\mu^*)}$ (Assumption 3): its coordinates are independent with $\mathbb P(Q_u(0)=n)=(1-\rho_u)\rho_u^n$. The **genie queue** always uses the optimal server and shares arrivals, services and initial state with the system:
--   $$Q^*_u(0)=Q_u(0),\qquad Q^*_u(t)=\big(Q^*_u(t-1)+A_u(t)-R_{uk^*_u}(t)\big)^+.$$
--
--   These objects are the common ground of every statement of the mission: the late-stage lemmas compare the queue under Q-UCB with $Q^*$ on this space.
--
--   **Formalization Note** Queues and servers are `Fin U` and `Fin K` (0-based); slots are $t\ge1$ and seed $0$ is unused. Truncated natural subtraction implements $(\cdot)^+$. The geometric product law is the stationary law of the genie chain under the printed recursion (a birth–death chain with up-probability $\lambda_u(1-\mu^*_u)$ and down-probability $(1-\lambda_u)\mu^*_u$); the page's tail formula belongs to a different convention (paper.md slip 5). The coupling $Q^*(0)=Q(0)$ with shared $A,R$ is implicit in the paper's proofs (Lemma 12, Theorem 5) and leaves $\Psi_u(t)$ unchanged. $\Delta$ is defined as $0$ when $K=1$ or $U=0$, a value never used since every statement assumes $K\ge2$ and names a queue $u$.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, pp. 6–8, §3.2, Assumptions 1–3; p. 15, Algorithm 1 (explore coin)

import Mathlib

namespace QueueBandit.QUCB

open MeasureTheory ProbabilityTheory

/-- A problem instance `(λ, μ)` of the `U × K` switch (§3.2, pp. 7–8): arrival probabilities
`lam u`, service probabilities `mu u k`, all in `[0, 1]`, together with the optimal server map
`kstar` of Assumption 1 (unique optimal server per queue, optimal servers pairwise distinct) and
the stability condition of Assumption 2 (`ε_u = μ*_u − λ_u > 0`). Queues are `Fin U`, servers
`Fin K` (0-based indices for the paper's `[U]`, `[K]`). -/
structure Instance (U K : ℕ) where
  lam : Fin U → ℝ
  mu : Fin U → Fin K → ℝ
  kstar : Fin U → Fin K
  lam_nonneg : ∀ u, 0 ≤ lam u
  lam_le_one : ∀ u, lam u ≤ 1
  mu_nonneg : ∀ u k, 0 ≤ mu u k
  mu_le_one : ∀ u k, mu u k ≤ 1
  /-- Assumption 1(2): the optimal queue–server pairs form a matching. -/
  kstar_injective : Function.Injective kstar
  /-- Assumption 1(1): `k*_u` is the unique best server of queue `u`. -/
  kstar_unique : ∀ u k, k ≠ kstar u → mu u k < mu u (kstar u)
  /-- Assumption 2 (stability): `λ_u < μ*_u` for every queue. -/
  stable : ∀ u, lam u < mu u (kstar u)

variable {U K : ℕ}

/-- `μ*_u = max_k μ_uk = μ_{u k*_u}`. -/
def Instance.muStar (I : Instance U K) (u : Fin U) : ℝ := I.mu u (I.kstar u)

/-- The load gap `ε_u = μ*_u − λ_u`. -/
def Instance.eps (I : Instance U K) (u : Fin U) : ℝ := I.muStar u - I.lam u

/-- The sub-optimal pairs `{(u, k) : k ≠ k*_u}`. -/
def Instance.subPairs (I : Instance U K) : Finset (Fin U × Fin K) :=
  Finset.univ.filter fun p => p.2 ≠ I.kstar p.1

/-- `Δ = min_{u, k ≠ k*_u} (μ*_u − μ_uk)`; a genuine minimum whenever `U ≥ 1` and `K ≥ 2`
(the set is then nonempty); the value `0` on an empty set is never used. -/
noncomputable def Instance.gap (I : Instance U K) : ℝ :=
  if h : I.subPairs.Nonempty then I.subPairs.inf' h (fun p => I.muStar p.1 - I.mu p.1 p.2) else 0

/-- `ρ_u = λ_u(1 − μ*_u) / ((1 − λ_u) μ*_u)`, the ratio of up- and down-transition probabilities of
the genie queue `u` under the recursion `Q(t) = (Q(t−1) + A(t) − S(t))⁺`; `ρ_u ∈ [0, 1)` under
Assumption 2. -/
noncomputable def Instance.rho (I : Instance U K) (u : Fin U) : ℝ :=
  I.lam u * (1 - I.muStar u) / ((1 - I.lam u) * I.muStar u)

/-- Assumption 3: the law `π_(λ, μ*)` of `Q(0)`, the product over queues of the geometric laws
`P(Q_u(0) = n) = (1 − ρ_u) ρ_u ^ n`, i.e. the stationary law of the genie queues. -/
noncomputable def Instance.initLaw (I : Instance U K) : Measure (Fin U → ℕ) :=
  Measure.sum fun q : Fin U → ℕ =>
    ENNReal.ofReal (∏ u, (1 - I.rho u) * I.rho u ^ q u) • Measure.dirac q

/-- A matching: an injective assignment of a server to every queue (`ℳ ⊂ [K]^U`, p. 14). -/
abbrev Matching (U K : ℕ) := {κ : Fin U → Fin K // Function.Injective κ}

/-- The randomness of one time slot: a uniform `W u` per arrival, a uniform `V (u, k)` per link,
a uniform coin `ξ` for the explore decision, and an explore index `J ∈ Fin K`. -/
abbrev Seed (U K : ℕ) := (Fin U → unitInterval) × ((Fin U × Fin K → unitInterval) × (unitInterval × Fin K))

/-- The uniform law on `Fin K` (a probability measure for `K ≥ 1`). -/
noncomputable def uniformFin (K : ℕ) : Measure (Fin K) := (K : ENNReal)⁻¹ • Measure.count

/-- The law of one slot's seed: independent uniforms on `[0, 1]` and a uniform index on `Fin K`. -/
noncomputable def seedLaw (U K : ℕ) : Measure (Seed U K) :=
  (Measure.pi fun _ : Fin U => (volume : Measure unitInterval)).prod
    ((Measure.pi fun _ : Fin U × Fin K => (volume : Measure unitInterval)).prod
      ((volume : Measure unitInterval).prod (uniformFin K)))

/-- The sample space: the initial queue vector `Q(0)` and the i.i.d. seeds of slots `0, 1, 2, …`
(slot `0` is unused; time slots are `t ≥ 1`). -/
abbrev Ω (U K : ℕ) := (Fin U → ℕ) × (ℕ → Seed U K)

/-- The probability measure: `Q(0) ~ π_(λ, μ*)` independent of the i.i.d. seeds. -/
noncomputable def Instance.P (I : Instance U K) : Measure (Ω U K) :=
  I.initLaw.prod (Measure.infinitePi fun _ : ℕ => seedLaw U K)

/-- Arrival `A_u(t) = 1{W_u(t) ≤ λ_u}`, Bernoulli(λ_u). -/
noncomputable def Instance.A (I : Instance U K) (u : Fin U) (t : ℕ) (ω : Ω U K) : ℕ :=
  if ((ω.2 t).1 u : ℝ) ≤ I.lam u then 1 else 0

/-- Potential service of link `(u, k)` in slot `t`: `R_uk(t) = 1{V_uk(t) ≤ μ_uk}`, Bernoulli(μ_uk). -/
noncomputable def Instance.R (I : Instance U K) (u : Fin U) (k : Fin K) (t : ℕ) (ω : Ω U K) : ℕ :=
  if ((ω.2 t).2.1 (u, k) : ℝ) ≤ I.mu u k then 1 else 0

/-- The genie queue `Q*_u`: always served by `k*_u`, same arrivals, services and initial state as
the system under the algorithm, `Q*_u(t) = (Q*_u(t−1) + A_u(t) − R_{u k*_u}(t))⁺` (truncated `ℕ`
subtraction is exactly `(·)⁺`). -/
noncomputable def Instance.Qstar (I : Instance U K) (u : Fin U) : ℕ → Ω U K → ℕ
  | 0, ω => ω.1 u
  | t + 1, ω => I.Qstar u t ω + I.A u (t + 1) ω - I.R u (I.kstar u) (t + 1) ω

/-- The explore probability `min{1, 3K log² t / t}` of Algorithm 1. -/
noncomputable def exploreProb (K t : ℕ) : ℝ := min 1 (3 * K * Real.log t ^ 2 / t)

/-- The explore indicator `E(t) = 1{ξ_t < min{1, 3K log² t / t}}`, Bernoulli with that mean and
independent across slots. -/
noncomputable def explore (t : ℕ) (ω : Ω U K) : ℕ :=
  if (((ω.2 t).2.2.1 : unitInterval) : ℝ) < exploreProb K t then 1 else 0

end QueueBandit.QUCB


