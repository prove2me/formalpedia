-- Prove2me | Definitions.Def_MinorityDynamics_Kernel
-- name    : MinorityDynamics_Kernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:45.000576+00:00
-- url     : https://prove2.me/theorems/4a17e7f5-f212-4181-a5c1-243465aa5dbd
-- title:
--   Probabilities of staying in sets and of avoiding a set; total variation distance
-- statement:
--   Let $P=(P(x,y))_{x,y\in\mathcal X}$ be the transition matrix of a Markov chain $(X_t)_{t\ge0}$ on a finite state space $\mathcal X$. The module defines:
--
--   1. For a family of sets $G_0,G_1,\dots\subseteq\mathcal X$ and $d\in\mathbb N$, the probability
--   $$\mathrm{stay}_P(G,d,x)=\Pr_x\big(X_t\in G_t\ \text{for all }0\le t\le d\big),$$
--   computed by the first-step recursion $\mathrm{stay}_P(G,0,x)=\mathbf 1[x\in G_0]$ and $\mathrm{stay}_P(G,d+1,x)=\mathbf 1[x\in G_0]\sum_y P(x,y)\,\mathrm{stay}_P(G_{\cdot+1},d,y)$.
--   2. The probability of avoiding a set $A$ during rounds $0,\dots,t$,
--   $$\mathrm{avoid}_P(A,t,x)=\Pr_x(X_0\notin A,\dots,X_t\notin A)=\Pr_x(\tau_A>t),\qquad \tau_A=\inf\{t\ge0:X_t\in A\}.$$
--   3. The total variation distance of two probability vectors $\mu,\nu$ on $\mathcal X$, $d_{TV}(\mu,\nu)=\tfrac12\sum_x|\mu(x)-\nu(x)|$.
--
--   These are the probabilistic events of the paper: hitting times $\tau_{\mathcal H}$ and $\tau_0$ (Lemmas 3.1, 3.2, 8.3, 8.6, Theorem 1.1), the joint tracking events of Lemmas 6.3 and 7.3, and the one-step comparison of Lemma 2.2.
--
--   **Formalization Note** No trajectory measure is constructed: the recursion is the probability of the event under the law of the chain started at $x$ (Markov property). An event $\tau_A>T$ with a real $T\ge0$ is $\tau_A>\lfloor T\rfloor$.
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), §3, p.13 (τ_H, τ_0); Lemma 2.2, p.12 (total variation); Lemma 6.3, p.34 and Lemma 7.3, p.38 (joint events)

import Mathlib

set_option autoImplicit false

namespace MinorityDynamics

open Classical

/-- **Staying in a time-dependent family of sets** for a Markov chain on a finite state space
with transition matrix `P` (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small
Samples*, manuscript (STOC 2027 submission); used for the events of Lemma 6.3, p.34 = PDF p.36,
and Lemma 7.3, p.38 = PDF p.40).

`stayProb P G d x` is the probability, for the chain started at `X₀ = x`, that `Xₜ ∈ G t` for
every `0 ≤ t ≤ d`. It is defined by the first-step recursion
`stayProb P G 0 x = 1[x ∈ G 0]` and
`stayProb P G (d+1) x = 1[x ∈ G 0] · ∑ y, P x y · stayProb P (fun t => G (t+1)) d y`.

**Formalization Note** `P x y` is the one-step probability of moving from `x` to `y`, a real
number. No trajectory measure is built: for a stochastic matrix `P` this recursion is the
probability of the event under the law of the chain, by the Markov property. -/
noncomputable def stayProb {α : Type*} [Fintype α] (P : α → α → ℝ) :
    (ℕ → Set α) → ℕ → α → ℝ
  | G, 0, x => if x ∈ G 0 then 1 else 0
  | G, d + 1, x => if x ∈ G 0 then ∑ y, P x y * stayProb P (fun t => G (t + 1)) d y else 0

/-- **Avoiding a set during rounds `0, …, t`**: `avoidProb P A t x = Pr_x(X₀ ∉ A, …, Xₜ ∉ A)
= Pr_x(τ_A > t)`, where `τ_A = inf{t ≥ 0 : Xₜ ∈ A}` is the hitting time of `A` (manuscript, §3,
p.13 = PDF p.15: `τ_H`, `τ₀`).

**Formalization Note** The paper's events `τ_A > s` for a real `s ≥ 0` are `τ_A > ⌊s⌋`, i.e.
`avoidProb P A ⌊s⌋₊ x`, since `τ_A` is an integer. -/
noncomputable def avoidProb {α : Type*} [Fintype α] (P : α → α → ℝ) (A : Set α) (t : ℕ)
    (x : α) : ℝ :=
  stayProb P (fun _ => Aᶜ) t x

/-- The **total variation distance** of two probability vectors `μ, ν` on a finite type,
`d_TV(μ, ν) = (1/2) ∑ₓ |μ x − ν x|` (manuscript, Lemma 2.2, p.12 = PDF p.14).

**Formalization Note** For probability vectors this equals `max_A |μ(A) − ν(A)|`. -/
noncomputable def tvDist {α : Type*} [Fintype α] (μ ν : α → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |μ x - ν x|

end MinorityDynamics


