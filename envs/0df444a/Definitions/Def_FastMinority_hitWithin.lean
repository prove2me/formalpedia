-- Prove2me | Definitions.Def_FastMinority_hitWithin
-- name    : FastMinority_hitWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:22.572365+00:00
-- url     : https://prove2.me/theorems/02b16b6c-0d0b-4566-af72-62f28cb9fc2f
-- title:
--   Hitting a set within $N$ steps at a prescribed place
-- statement:
--   Let $P$ be the transition matrix of a Markov chain on a finite state space, $A$ and $B$ sets of states, and $\tau_A=\inf\{t\ge0:X_t\in A\}$. For a horizon $N$,
--   $$
--   h_N(x)=\Pr_x\big(\tau_A\le N,\ X_{\tau_A}\in B\big),
--   $$
--   defined by $h_0(x)=\mathbf 1[x\in A\cap B]$ and $h_{N+1}(x)=\mathbf 1[x\in A\cap B]$ for $x\in A$, $h_{N+1}(x)=\sum_y P(x,y)h_N(y)$ for $x\notin A$. It is nondecreasing in $N$ and converges to $\Pr_x(\tau_A<\infty,X_{\tau_A}\in B)$.
--
--   It expresses the events of Lemma 3.6 ($A=\mathcal L^c$, $B=\mathcal C\cup\mathcal H^+$) and Lemma 5.18 ($A=\mathcal C$, $B=\{j\}$).
--
--   **Formalization Note** Defined by the recursion, with no trajectory measure; for a stochastic matrix it is the probability of the event by the Markov property.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Lemma 3.6, p.10 (PDF p.12), and Lemma 5.18, p.35 (PDF p.37)

import Mathlib

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Hitting a set within a horizon, at a prescribed place** (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1); used for the events
`{τ_𝓛 < ∞, X_{τ_𝓛} ∈ 𝓒 ∪ 𝓗⁺}` of Lemma 3.6, p.10 = PDF p.12, and `{τ < ∞, X_τ = j}` of
Lemma 5.18, p.35 = PDF p.37).

For a Markov chain with transition matrix `P` on a finite state space, `τ_A = inf{t ≥ 0 : X_t ∈ A}`,
and `hitWithin P A B N x = Pr_x(τ_A ≤ N, X_{τ_A} ∈ B)`, defined by the first-step recursion
`hitWithin P A B 0 x = 1[x ∈ A ∩ B]` and
`hitWithin P A B (N + 1) x = 1[x ∈ A ∩ B]` if `x ∈ A`, `∑ y, P x y · hitWithin P A B N y` otherwise.

**Formalization Note** No trajectory measure is built: for a stochastic matrix `P` the recursion is
the probability of the event, by the Markov property. It is nondecreasing in `N`, and its limit is
`Pr_x(τ_A < ∞, X_{τ_A} ∈ B)`. -/
noncomputable def hitWithin {α : Type*} [Fintype α] (P : α → α → ℝ) (A B : Set α) :
    ℕ → α → ℝ
  | 0, x => if x ∈ A then (if x ∈ B then 1 else 0) else 0
  | N + 1, x => if x ∈ A then (if x ∈ B then 1 else 0) else ∑ y, P x y * hitWithin P A B N y

end FastMinority


