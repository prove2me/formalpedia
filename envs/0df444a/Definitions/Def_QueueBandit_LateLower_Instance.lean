-- Prove2me | Definitions.Def_QueueBandit_LateLower_Instance
-- name    : QueueBandit_LateLower_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:19.310886+00:00
-- url     : https://prove2.me/theorems/b8570644-a60f-4dac-8af4-1ced744d85df
-- title:
--   §3.2, pp. 7–8, (2) p. 11 — switch instance (λ, μ), Assumption 1, Δ, μ_min, μ*, λ_min, Bernoulli KL and D(μ)
-- statement:
--   A **multi-queue switch network** has $U$ queues and $K$ servers. A **problem instance** is a pair $(\lambda,\mu)$ of arrival probabilities $\lambda=(\lambda_u)_{u\in[U]}$ and service probabilities $\mu=(\mu_{uk})_{u\in[U],k\in[K]}$, all in $[0,1]$.
--
--   **Assumption 1 (unique optimal matching).** There is a map $k^*:[U]\to[K]$ such that
--
--   1. for every queue $u$, $k^*_u$ is the unique best server: $\mu_{uk}<\mu_{uk^*_u}$ for all $k\neq k^*_u$;
--   2. distinct queues have distinct best servers: $u\neq u'$ implies $k^*_u\neq k^*_{u'}$.
--
--   Write $\mu^*_u=\mu_{uk^*_u}$. The derived quantities are the gaps and extremes
--   $$\Delta_{uk}=\mu^*_u-\mu_{uk},\qquad \Delta=\min_{u\in[U],\,k\neq k^*_u}\Delta_{uk},\qquad \mu_{\min}=\min_{u,k}\mu_{uk},\qquad \mu^*=\max_{u,k}\mu_{uk},\qquad \lambda_{\min}=\min_u\lambda_u .$$
--   With the Bernoulli Kullback–Leibler divergence (the published definition `RegretBandits.Stochastic.klBern`)
--   $$\mathrm{KL}(p,q)=p\log\frac pq+(1-p)\log\frac{1-p}{1-q},$$
--   the instance constant of display (2) is
--   $$D(\mu)=\frac{\Delta}{\mathrm{KL}\big(\mu_{\min},\frac{\mu^*+1}{2}\big)}.$$
--   The factor $1/\mathrm{KL}(\mu_{\min},(\mu^*+1)/2)$ of Lemma 19 is defined alongside it.
--
--   These are the instance-level objects on which the lower bounds of the paper are stated.
--
--   **Formalization Note** Queues and servers are indexed by `Fin U` and `Fin K` (0-based). The optimal matching is carried as data `kstar` together with Assumption 1, which determines it uniquely. The minima and maxima are finite `inf'`/`sup'`; on an empty index set they return $0$, which never happens under the hypotheses $U\ge1$, $K\ge2$ used by every theorem. When $\mu^*=1$ the divergence $\mathrm{KL}(\mu_{\min},1)$ is $+\infty$, so $D(\mu)$ and $1/\mathrm{KL}$ are defined to be $0$ in that case. The divergence is not redefined here: the module imports the published `RegretBandits.Stochastic.klBern` and re-exports it as `klBern`. Lean's conventions $0\log 0=0$ make $\mathrm{KL}(0,q)=\log\frac1{1-q}$, as in the paper.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 7, §3.2 (notation); pp. 7–8, Assumption 1; p. 11, display (2)

import Mathlib
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

namespace QueueBandit.LateLower

open Finset

variable {U K : ℕ}

/-- Assumption 1 (unique optimal matching), Krishnasamy–Sen–Johari–Shakkottai, pp. 7–8.
`kstar u` is the optimal server of queue `u`: it is the unique maximiser of `mu u ·`
(`Δ_uk > 0` for `k ≠ k*_u`), and distinct queues have distinct optimal servers. -/
def Assumption1 (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K) : Prop :=
  Function.Injective kstar ∧ ∀ u k, k ≠ kstar u → mu u k < mu u (kstar u)

/-- A problem instance `(λ, μ)` of the switch with `U` queues and `K` servers: arrival and
service probabilities in `[0, 1]`, together with the optimal matching `kstar` of Assumption 1. -/
def IsInstance (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K) : Prop :=
  (∀ u, 0 ≤ lam u ∧ lam u ≤ 1) ∧ (∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1) ∧ Assumption1 mu kstar

/-- The service-rate gap `Δ_uk = μ*_u − μ_uk`, with `μ*_u = μ_{u k*_u}`. -/
def gap (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K) (u : Fin U) (k : Fin K) : ℝ :=
  mu u (kstar u) - mu u k

/-- The pairs `(u, k)` with `k ≠ k*_u`. -/
def subPairs (kstar : Fin U → Fin K) : Finset (Fin U × Fin K) :=
  univ.filter fun p => p.2 ≠ kstar p.1

/-- `Δ = min_{u, k ≠ k*_u} Δ_uk` (p. 7). The minimum is over a nonempty set whenever
`U ≥ 1` and `K ≥ 2`; the value `0` on the empty set is never used under those hypotheses. -/
noncomputable def gapMin (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K) : ℝ :=
  if h : (subPairs kstar).Nonempty then (subPairs kstar).inf' h (fun p => gap mu kstar p.1 p.2)
  else 0

/-- `μ_min = min_{u,k} μ_uk` (p. 7); `0` only when `U = 0` or `K = 0`. -/
noncomputable def muMin (mu : Fin U → Fin K → ℝ) : ℝ :=
  if h : (univ : Finset (Fin U × Fin K)).Nonempty then univ.inf' h (fun p => mu p.1 p.2) else 0

/-- `μ* = max_{u,k} μ_uk` (p. 7); `0` only when `U = 0` or `K = 0`. -/
noncomputable def muStar (mu : Fin U → Fin K → ℝ) : ℝ :=
  if h : (univ : Finset (Fin U × Fin K)).Nonempty then univ.sup' h (fun p => mu p.1 p.2) else 0

/-- `λ_min = min_u λ_u` (p. 7); `0` only when `U = 0`. -/
noncomputable def lamMin (lam : Fin U → ℝ) : ℝ :=
  if h : (univ : Finset (Fin U)).Nonempty then univ.inf' h lam else 0

/-! The Bernoulli Kullback–Leibler divergence
`KL(p, q) = p log(p/q) + (1 − p) log((1 − p)/(1 − q))` is the published
`RegretBandits.Stochastic.klBern`; it is re-exported here under the name `klBern`. -/
export RegretBandits.Stochastic (klBern)

/-- The factor `1 / KL(μ_min, (μ* + 1)/2)` of Lemma 19 (p. 37). When `μ* = 1` the divergence is
`+∞` and the factor is `0`. -/
noncomputable def invKL (mu : Fin U → Fin K → ℝ) : ℝ :=
  if muStar mu < 1 then (klBern (muMin mu) ((muStar mu + 1) / 2))⁻¹ else 0

/-- `D(μ) = Δ / KL(μ_min, (μ* + 1)/2)`, display (2), p. 11, with `D(μ) = 0` when `μ* = 1`
(the divergence is then `+∞`). -/
noncomputable def D (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K) : ℝ :=
  if muStar mu < 1 then gapMin mu kstar / klBern (muMin mu) ((muStar mu + 1) / 2) else 0

end QueueBandit.LateLower


