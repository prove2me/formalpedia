-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_PairLabel
-- name    : MatroidOptGame_Supplement_PairLabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:48:51.173195+00:00
-- url     : https://prove2.me/theorems/9fb5d305-c3f3-4a2f-b3f2-ba12f809af12
-- title:
--   Labels $(S_0,\pi)$ of the family $\mathcal M_{n,S_0,\pi}$
-- statement:
--   For $n\ge 1$, a **label** of the family $\mathcal M_{n,S_0,\pi}$ is a pair $(S_0,\pi)$ where
--
--   1. $S_0\subseteq E_n=\{0,\dots,2n-1\}$ has $|S_0|=n$, $0\in S_0$ and $1\notin S_0$ (so $1\in S_1=E_n\setminus S_0$);
--   2. $\pi:E_n\to E_n$ is an involution, $\pi(\pi(i))=i$, exchanging $S_0$ and $S_1$ ($i\in S_0\iff\pi(i)\notin S_0$);
--   3. $\pi(0)=1$.
--
--   The paper's labels are partitions $S_0\sqcup S_1$ with a bijection $\pi:S_0\to S_1$, $\pi(0)=1$; restricting the involution to $S_0$ identifies the two label sets. In Theorem 11 the hidden matroid is drawn from the uniform distribution on these labels.
--
--   **Formalization Note** Several labels give the same matroid; the law is on labels, as in the paper ("the uniform distribution on the choice of $S_0,\pi$", p.12). The label set is a finite subtype of $\mathrm{Finset}(\mathrm{Fin}\,2n)\times(\mathrm{Fin}\,2n\to\mathrm{Fin}\,2n)$.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.1, p.11 (family), p.12 (uniform law)

import Mathlib

namespace MatroidOptGame.Supplement

/-- The labels `(S₀, π)` of the Theorem 11 family `M_{n,S₀,π}`: `S₀ ⊆ E_n = Fin (2n)` with
`|S₀| = n`, `0 ∈ S₀`, `1 ∉ S₀` (so `1 ∈ S₁ = E_n ∖ S₀`), and `π` a fixed-point-free involution of
`E_n` exchanging `S₀` and `S₁` with `π(0) = 1`.
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.1, p.11 ("for every partition S₀ ⊔ S₁ = {0, 1, 2, …, 2n − 1} into two
equal-sized sets satisfying 0 ∈ S₀ and 1 ∈ S₁, and for every 1-1 mapping π : S₀ → S₁ satisfying
π(0) = 1"; "extend π to S₁ by putting π(j) = i such that i ∈ S₀ and π(i) = j").
**Formalization Note.** The paper's label is a pair (`S₀`, bijection `S₀ → S₁`); restricting the
involution to `S₀` is a bijection between those labels and these, so the uniform law on these
labels is the paper's uniform law "on the choice of S₀, π" (p.12). Elements `0` and `1` are named
by their values, since `Fin (2n)` has no literals for variable `n`. Several labels give the same
matroid; the law is on labels, as in the paper. -/
abbrev PairLabel (n : ℕ) : Type :=
  {ℓ : Finset (Fin (2 * n)) × (Fin (2 * n) → Fin (2 * n)) //
    ℓ.1.card = n ∧ (∀ i : Fin (2 * n), i.val = 0 → i ∈ ℓ.1) ∧
    (∀ i : Fin (2 * n), i.val = 1 → i ∉ ℓ.1) ∧ (∀ i, ℓ.2 (ℓ.2 i) = i) ∧
    (∀ i, i ∈ ℓ.1 ↔ ℓ.2 i ∉ ℓ.1) ∧ (∀ i : Fin (2 * n), i.val = 0 → (ℓ.2 i).val = 1)}

end MatroidOptGame.Supplement


