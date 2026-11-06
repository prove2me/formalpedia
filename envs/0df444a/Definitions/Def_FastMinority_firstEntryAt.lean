-- Prove2me | Definitions.Def_FastMinority_firstEntryAt
-- name    : FastMinority_firstEntryAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:24.972496+00:00
-- url     : https://prove2.me/theorems/90c15032-8d7d-43bb-93a3-a84027b1069c
-- title:
--   Taboo probabilities $P^\ell(i,j\mid \cdot)$ of a finite Markov chain
-- statement:
--   Let $P$ be the transition matrix of a Markov chain on a finite state space and $A$ a set of states. For $\ell\ge1$ and states $i,j$,
--   $$
--   P^\ell_A(i,j)=\Pr_i\big(X_1\notin A,\dots,X_{\ell-1}\notin A,\ X_\ell=j\big),
--   $$
--   the total probability of the trajectories of length $\ell$ from $i$ to $j$ whose intermediate states lie outside $A$. It satisfies $P^1_A(i,j)=P(i,j)$ and $P^{\ell+1}_A(i,j)=\sum_{y\notin A}P(i,y)P^{\ell}_A(y,j)$. For $j\in A$ it is the probability that the first visit to $A$ after time $0$ happens at time $\ell$ and at $j$; with $A=\mathcal C\cup\mathcal H^+$ these are the source's $P^\ell(i,j\mid\mathcal L\cup\mathcal U)$.
--
--   **Formalization Note** Defined by the recursion above (value $0$ at $\ell=0$), with no trajectory measure; for a stochastic matrix this is the probability of the event by the Markov property.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 3, p.7 (PDF p.9)

import Mathlib

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Taboo transition probabilities** of a Markov chain with transition matrix `P` on a finite
state space (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §3, p.7 = PDF p.9: "`P^ℓ(i, j | 𝓛 ∪ 𝓤)` denote the total probability of all
trajectories `X_t, … X_{t+ℓ}` of length `ℓ` with `X_t = i` and `X_{t+ℓ} = j` whose intermediate
states `X_{t+1}, … X_{t+ℓ−1}` lie entirely in" the taboo complement).

`firstEntryAt P A ℓ i j = Pr_i(X_1 ∉ A, …, X_{ℓ−1} ∉ A, X_ℓ = j)` for `ℓ ≥ 1`: the first-step
recursion `firstEntryAt P A 1 i j = P i j` and
`firstEntryAt P A (ℓ + 2) i j = ∑_{y ∉ A} P i y · firstEntryAt P A (ℓ + 1) y j`; the value at
`ℓ = 0` is `0`. For `j ∈ A` it is the probability that the first visit to `A` after time `0` happens
at time `ℓ` and at `j`.

**Formalization Note** No trajectory measure is built: for a stochastic matrix `P` this recursion is
the probability of the event, by the Markov property. -/
noncomputable def firstEntryAt {α : Type*} [Fintype α] (P : α → α → ℝ) (A : Set α) :
    ℕ → α → α → ℝ
  | 0, _, _ => 0
  | 1, i, j => P i j
  | ℓ + 2, i, j => ∑ y, (if y ∈ A then 0 else P i y) * firstEntryAt P A (ℓ + 1) y j

end FastMinority


