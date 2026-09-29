-- Prove2me | Definitions.Def_PermLimits_Shared_PermDensity
-- name    : PermLimits_Shared_PermDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:55:05.868762+00:00
-- url     : https://prove2.me/theorems/d9bfc26e-01f6-41e7-9c8b-b1cdfe1a592f
-- title:
--   Subpermutation density $t(\tau,\pi)$ and convergent permutation sequences
-- statement:
--   This bundle fixes the finite objects of the theory of permutation limits.
--
--   For a positive integer $n$ let $S_n$ be the set of permutations of $[n]=\{1,\dots,n\}$, and write $|\pi| = n$ for $\pi \in S_n$. A *permutation sequence* is a sequence $(\sigma_m)_{m\in\mathbb N}$ of permutations of possibly different lengths.
--
--   1. **Occurrences.** For $\tau \in S_k$ and $\pi \in S_n$, the number of occurrences $\Lambda(\tau,\pi)$ of $\tau$ in $\pi$ is the number of $k$-tuples $x_1 < x_2 < \dots < x_k$ in $[n]$ such that $\pi(x_i) < \pi(x_j)$ if and only if $\tau(i) < \tau(j)$.
--   2. **Subpermutation density.** The density of $\tau$ as a subpermutation of $\pi$ is
--   $$t(\tau,\pi) = \begin{cases} \binom{n}{k}^{-1}\Lambda(\tau,\pi) & \text{if } k \le n,\\ 0 & \text{if } k > n.\end{cases}$$
--   3. **Convergent sequence.** A permutation sequence $(\sigma_m)$ is *convergent* if for every fixed permutation $\tau$ the real sequence $(t(\tau,\sigma_m))_m$ converges.
--
--   For example, $\tau=(3,1,4,2)$ occurs in $\pi=(5,6,2,4,7,1,3)$ at the positions $(1,3,5,7)$. The densities $t(\tau,\cdot)$ play for permutations the role that homomorphism densities play for graphs; convergence in the sense of item 3 is what a limit object has to capture.
--
--   **Formalization Note** Permutations of $[n]$ are permutations of $\{0,\dots,n-1\}$ (`Equiv.Perm (Fin n)`); the shift does not change relative orders. A permutation of arbitrary length is a pair $\langle n, \pi\rangle$, and a sequence is a map from $\mathbb N$ to such pairs. The type allows length $0$; a pattern of length $0$ has density $1$ in every permutation, so quantifying over all lengths adds only a trivially satisfied condition. The case $k>n$ is written explicitly rather than through division by zero. The source's Eq. (3) misprints $\Lambda(\tau,\sigma)$ for $\Lambda(\tau,\pi)$.
--
--   This definition is shared by both missions of this series: mission 1 (`01-limit-existence`, existence and uniqueness of the limit permutation) (Theorem 1.6, p. 4; Theorem 1.7, p. 5; Lemma 3.5, p. 11; Definition 1.5, p. 4) and mission 2 (`02-cauchy-rectangular`, convergent sequences are Cauchy for the rectangular distance) (Theorem 1.6 (i), p. 4; Theorem 1.8, p. 5; Claim 2.4, p. 9; Lemma 3.5, p. 11; Definition 1.5, p. 4).
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 3, Definition 1.1 (Eq. (3)) and Definition 1.2

import Mathlib

/-!
# Subpermutation density and convergent permutation sequences

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2, p. 3, Definitions 1.1 and 1.2, Eq. (3).

A definition bundle: the number of occurrences `Λ(τ, π)`, the density `t(τ, π)`, and the notion of
a convergent permutation sequence.

**Formalization Note.** The paper's `S_n` (permutations of `[n] = {1, …, n}`) is
`Equiv.Perm (Fin n)`, i.e. permutations of `{0, …, n-1}`; the shift by one changes no relative
order, so `Λ` and `t` are unchanged. A permutation of arbitrary length (an element of the paper's
`𝒮 = ⋃ₙ Sₙ`) is a dependent pair `⟨n, π⟩ : Σ n : ℕ, Equiv.Perm (Fin n)`, and a permutation
sequence is a map `ℕ → Σ n : ℕ, Equiv.Perm (Fin n)`; `|σ_m|` is `(σ m).1`. Length `0` is allowed
by the type. A length-`0` pattern `τ` has `t(τ, π) = 1` for every `π` (and `t(τ, Z) = 1` for every
limit permutation), so quantifying over all `k`, including `k = 0`, adds only a trivially
satisfied clause.
-/

namespace PermLimits.Shared

open Filter Topology

/-- **Occurrences** `Λ(τ, π)` (Hoppen et al., arXiv:1103.5844v2, Definition 1.1, p. 3).
For `τ ∈ S_k` and `π ∈ S_n`, the number of strictly increasing `k`-tuples
`x₁ < x₂ < … < x_k` in `[n]` such that `π(x_i) < π(x_j)` if and only if `τ(i) < τ(j)`.

**Formalization Note.** A strictly increasing `k`-tuple in `[n]` is a map `x : Fin k → Fin n`
with `i < j → x i < x j`; indices are 0-based (see the module note). -/
noncomputable def occurrences {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) : ℕ :=
  open Classical in
  (Finset.univ.filter (fun x : Fin k → Fin n =>
    (∀ i j, i < j → x i < x j) ∧ ∀ i j, (π (x i) < π (x j) ↔ τ i < τ j))).card

/-- **Subpermutation density** `t(τ, π)` (Hoppen et al., arXiv:1103.5844v2, Definition 1.1,
Eq. (3), p. 3): `t(τ, π) = Λ(τ, π) / C(n, k)` if `k ≤ n`, and `0` if `k > n`.

**Formalization Note.** Eq. (3) of the preprint misprints `Λ(τ, σ)` for `Λ(τ, π)`. The case
`k > n` is written explicitly (it does not rely on division by zero; for `k > n` also
`Λ(τ, π) = 0`). -/
noncomputable def permDensity {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) : ℝ :=
  if k ≤ n then (occurrences τ π : ℝ) / (Nat.choose n k : ℝ) else 0

/-- **Convergent permutation sequence** (Hoppen et al., arXiv:1103.5844v2, Definition 1.2,
p. 3). A permutation sequence `(σ_m)` is convergent if, for every fixed permutation `τ`, the
sequence of real numbers `(t(τ, σ_m))_m` converges.

**Formalization Note.** No condition on the lengths `|σ_m|` is part of this definition (as in the
paper); `τ` ranges over permutations of every length `k` (see the module note on `k = 0`). -/
def IsConvergent (σ : ℕ → Σ n : ℕ, Equiv.Perm (Fin n)) : Prop :=
  ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)), ∃ L : ℝ,
    Tendsto (fun m => permDensity τ (σ m).2) atTop (𝓝 L)

end PermLimits.Shared


