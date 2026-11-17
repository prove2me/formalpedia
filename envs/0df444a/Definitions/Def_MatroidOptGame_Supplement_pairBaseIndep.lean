-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_pairBaseIndep
-- name    : MatroidOptGame_Supplement_pairBaseIndep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:48:39.458188+00:00
-- url     : https://prove2.me/theorems/61b5a3ea-dd9f-4350-bc52-34edd31288fe
-- title:
--   Independent sets of the matroid $\mathcal M_{n,S_0,\pi}$
-- statement:
--   Let $E_n=\{0,\dots,2n-1\}$, let $S_0\subseteq E_n$ and let $\pi$ be a pairing of $E_n$ (an involution exchanging $S_0$ and $S_1=E_n\setminus S_0$). A set $S\subseteq E_n$ is a **transversal** if it contains exactly one element of every pair $\{i,\pi(i)\}$. The set $S$ is **independent** in $\mathcal M_{n,S_0,\pi}$ if
--
--   1. $|S|\le n-1$; or
--   2. $|S|=n$ and $S$ contains both $i$ and $\pi(i)$ for some $i$; or
--   3. $|S|=n$, $S$ is a transversal and $|S\cap S_1|$ is even.
--
--   Sets with more than $n$ elements are dependent, so the rank is $n$. The bases are the $n$-sets containing a pair and the even transversals; odd transversals are the only dependent $n$-sets. These matroids are the hidden instances of the oracle upper bound on MAX (Theorem 11) and, with $S_0$ the even elements, the base of the modified family $\mathcal M_{n,H}$ (Theorem 14).
--
--   **Formalization Note** Only the predicate is defined; that it is a matroid is Lemma 8 of the paper. $\pi$ is the paper's bijection $S_0\to S_1$ extended to $S_1$, so "some $i\in S_0$ with $i,\pi(i)\in S$" is written "some $i$ with $i,\pi(i)\in S$"; $S\cap S_1$ is $S\setminus S_0$.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.1, p.11

import Mathlib

namespace MatroidOptGame.Supplement

/-- Independence in the matroid `M_{n,S₀,π}` on `E_n = Fin (2n)`: given the side `S₀` and the
pairing `π` (an involution exchanging `S₀` and `S₁ = E_n ∖ S₀`), a set `S` is independent iff
`|S| ≤ n − 1`, or `|S| = n` and either `S` contains both elements `i, π(i)` of some pair, or `S`
is a **transversal** (exactly one element of every pair) with `|S ∩ S₁|` even.
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.1, p.11 ("Every cardinality n set that contains, for some i ∈ S₀, both i
and π(i) is independent. A set S that contains exactly one of the two elements for every such pair
(we shall call such a set a transversal) is independent iff |S ∩ S₁| is even. … So all sets of
size n − 1 or less are independent").
**Formalization Note.** `π` is the paper's bijection `S₀ → S₁` extended to `S₁` by `π(j) = i`
(p.11, "extend π to S₁"), so "some `i ∈ S₀` with `i, π(i) ∈ S`" is "some `i` with `i, π(i) ∈ S`".
`S ∩ S₁ = S ∖ S₀`. Sets of size `> n` are dependent (the rank is `n`). This is only the
predicate; that it is a matroid is Lemma 8 of the paper. -/
def pairBaseIndep (n : ℕ) (S₀ : Finset (Fin (2 * n))) (π : Fin (2 * n) → Fin (2 * n))
    (S : Finset (Fin (2 * n))) : Prop :=
  S.card < n ∨
    (S.card = n ∧
      ((∃ i ∈ S, π i ∈ S) ∨ ((∀ i, i ∈ S ↔ π i ∉ S) ∧ Even (S \ S₀).card)))

end MatroidOptGame.Supplement


