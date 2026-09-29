-- Prove2me | Definitions.Def_TamingMonster_CoordDescent_Setting
-- name    : TamingMonster_CoordDescent_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:08:22.78616+00:00
-- url     : https://prove2.me/theorems/b760d7f3-02f0-4f8a-b55f-7ea63e4c334f
-- title:
--   History, IPS estimate (Eq. (1)), estimated regret, smoothed projection $Q^\mu$, and (OP)
-- statement:
--   This file fixes the deterministic data of the optimization problem (OP) of Agarwal et al. (2014).
--
--   There are $K$ actions $A=\{0,\dots,K-1\}$, an arbitrary context set $X$, and a finite policy class $\Pi\subseteq A^X$. A **history** $H_t$ is a sequence of $t$ interaction records $(x_i,a_i,r_i(a_i),p_i(a_i))$, $i=1,\dots,t$: a context $x_i\in X$, the chosen action $a_i\in A$, its observed reward $r_i(a_i)\in[0,1]$, and the probability $p_i(a_i)\in(0,1]$ with which it was chosen.
--
--   1. **Empirical expectation.** $\widehat{\mathbb E}_{x\sim H_t}[f(x)]=\frac1t\sum_{i=1}^t f(x_i)$.
--   2. **Inverse propensity scoring** (Eq. (1)):
--   $$\widehat{\mathcal R}_t(\pi)=\frac1t\sum_{i=1}^t\frac{r_i(a_i)\,\mathbb 1\{\pi(x_i)=a_i\}}{p_i(a_i)}.$$
--   3. **Estimated regret** (§2.2): $\widehat{\mathrm{Reg}}_t(\pi)=\widehat{\mathcal R}_t(\pi_t)-\widehat{\mathcal R}_t(\pi)$ with $\pi_t\in\arg\max_{\pi'\in\Pi}\widehat{\mathcal R}_t(\pi')$, i.e. $\max_{\pi'\in\Pi}\widehat{\mathcal R}_t(\pi')-\widehat{\mathcal R}_t(\pi)$; and $b_\pi=\widehat{\mathrm{Reg}}_t(\pi)/(\psi\mu)$ with $\psi=100$.
--   4. **Weights and smoothed projection** (§2.1, §2.4): $\Delta^\Pi=\{Q\in\mathbb R^\Pi: Q(\pi)\ge0\ \forall\pi,\ \sum_\pi Q(\pi)\le1\}$, and for weights $Q$ and $\mu\ge0$,
--   $$Q^\mu(a\mid x)=(1-K\mu)\sum_{\pi\in\Pi:\ \pi(x)=a}Q(\pi)+\mu .$$
--   5. **The optimization problem (OP)** (p. 5): $Q$ solves (OP) for $(H_t,\mu)$ if $Q\in\Delta^\Pi$ and
--   $$\sum_{\pi\in\Pi}Q(\pi)b_\pi\le 2K\quad(2),\qquad \widehat{\mathbb E}_{x\sim H_t}\Bigl[\frac{1}{Q^{\mu}(\pi(x)\mid x)}\Bigr]\le 2K+b_\pi\ \ \forall\pi\in\Pi\quad(3).$$
--
--   These objects are the input and the target of the coordinate descent algorithm (Algorithm 2) and of its potential function.
--
--   **Formalization Note** Actions are `Fin K`; records are indexed by `Fin t` (0-based) instead of $1,\dots,t$. The paper allows $p\in[0,1]$; here $p_i(a_i)\in(0,1]$, because Eq. (1) divides by it and a chosen action has positive probability. Weights on $\Pi$ are real functions on the subtype of the `Finset` $\Pi$; $Q^\mu$ is built from the unnormalized $Q$ (no default policy). The maximum over $\Pi$ is `⨆` over the finite subtype, which is the true maximum when $\Pi$ is nonempty (every theorem assumes this).
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 3 (§2.1), p. 4 (Eq. (1), §2.2, §2.4), p. 5 ((OP), Eqs. (2)-(3))

import Mathlib

namespace TamingMonster.CoordDescent

variable {X : Type*} {K t : ℕ}

/-- A history `H_t` of `t` interaction records `(x_i, a_i, r_i(a_i), p_i(a_i))`, `i = 1, …, t`
(§2.1, p. 3), indexed here by `Fin t`: the context, the chosen action in `A = Fin K`, the observed
reward `r_i(a_i) ∈ [0,1]`, and the probability `p_i(a_i) ∈ (0,1]` with which the action was
chosen. (The paper writes `p ∈ [0,1]`; a taken action has positive probability, and Eq. (1)
divides by it.) -/
structure History (X : Type*) (K t : ℕ) where
  x : Fin t → X
  a : Fin t → Fin K
  r : Fin t → ℝ
  p : Fin t → ℝ
  r_mem : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1
  p_mem : ∀ i, p i ∈ Set.Ioc (0 : ℝ) 1

/-- The empirical expectation `Ê_{x∼H_t}[f(x)] = (1/t) ∑_{i=1}^t f(x_i)`: a context drawn
uniformly from the `t` contexts of the history (§2.1). -/
noncomputable def empExp (H : History X K t) (f : X → ℝ) : ℝ :=
  (1 / (t : ℝ)) * ∑ i, f (H.x i)

/-- The inverse propensity scoring estimate, Eq. (1):
`R̂_t(π) = (1/t) ∑_{i=1}^t r_i(a_i) 1{π(x_i) = a_i} / p_i(a_i)`. -/
noncomputable def ipsEstimate (H : History X K t) (π : X → Fin K) : ℝ :=
  (1 / (t : ℝ)) * ∑ i, H.r i * (if π (H.x i) = H.a i then (1 : ℝ) else 0) / H.p i

/-- The estimated regret `R̂eg_t(π) = R̂_t(π_t) − R̂_t(π)` with `π_t ∈ argmax_{π' ∈ Π} R̂_t(π')`
(§2.2), written as `max_{π' ∈ Π} R̂_t(π') − R̂_t(π)` (the maximum over the finite class `Π`). -/
noncomputable def estRegret (Pi : Finset (X → Fin K)) (H : History X K t) (π : X → Fin K) : ℝ :=
  (⨆ π' : Pi, ipsEstimate H (π' : X → Fin K)) - ipsEstimate H π

/-- `b_π = R̂eg_t(π) / (ψ μ)` with `ψ = 100` ((OP), p. 5). -/
noncomputable def bCoef (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (π : X → Fin K) : ℝ :=
  estRegret Pi H π / (100 * μ)

/-- The smoothed projection of the (unnormalized) weights `Q` (§2.4):
`Q^μ(a | x) = (1 − Kμ) ∑_{π ∈ Π : π(x) = a} Q(π) + μ`. -/
noncomputable def smoothedProj (Pi : Finset (X → Fin K)) (μ : ℝ) (Q : Pi → ℝ) (x : X)
    (a : Fin K) : ℝ :=
  (1 - (K : ℝ) * μ) * (∑ π ∈ Finset.univ.filter (fun π : Pi => (π : X → Fin K) x = a), Q π) + μ

/-- `Q ∈ Δ^Π = {Q ∈ ℝ^Π : Q(π) ≥ 0 ∀ π ∈ Π, ∑_{π ∈ Π} Q(π) ≤ 1}` (§2.1). -/
def InSimplex (Pi : Finset (X → Fin K)) (Q : Pi → ℝ) : Prop :=
  (∀ π, 0 ≤ Q π) ∧ ∑ π, Q π ≤ 1

/-- `Q` is a solution to the optimization problem (OP) (p. 5) for history `H_t` and minimum
probability `μ`: `Q ∈ Δ^Π`,
(2) `∑_{π ∈ Π} Q(π) b_π ≤ 2K`, and
(3) `∀ π ∈ Π, Ê_{x∼H_t}[1 / Q^μ(π(x) | x)] ≤ 2K + b_π`. -/
def SolvesOP (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (Q : Pi → ℝ) : Prop :=
  InSimplex Pi Q ∧
  ∑ π, Q π * bCoef Pi H μ (π : X → Fin K) ≤ 2 * (K : ℝ) ∧
  ∀ π : Pi, empExp H (fun x => 1 / smoothedProj Pi μ Q x ((π : X → Fin K) x))
      ≤ 2 * (K : ℝ) + bCoef Pi H μ (π : X → Fin K)

end TamingMonster.CoordDescent


