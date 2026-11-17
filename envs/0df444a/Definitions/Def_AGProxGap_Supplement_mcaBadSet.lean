-- Prove2me | Definitions.Def_AGProxGap_Supplement_mcaBadSet
-- name    : AGProxGap_Supplement_mcaBadSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:14:47.600995+00:00
-- url     : https://prove2.me/theorems/7165c5c8-821f-49b7-92fd-593df7fa023d
-- title:
--   Parameters with an MCA-bad agreement witness
-- statement:
--   Let $C\subseteq K^n$ be a code over a finite field $K$, let $u_0,\dots,u_\ell\in K^n$ and $r(z)=\sum_{j=0}^{\ell}z^ju_j$, and let $e\ge0$ be an integer. An **$e$ agreement witness** is a triple $(z,c,A)$ with $z\in K$, $c\in C$, $A\subseteq[n]$, $|A|\ge n-e$ and $c|_A=r(z)|_A$. It is **MCA-bad** if no $c_0,\dots,c_\ell\in C$ satisfy $c_j|_A=u_j|_A$ for every $0\le j\le\ell$. The set defined here is
--   $$S=\{z\in K:\ \text{there is an MCA-bad } e \text{ agreement witness } (z,c,A)\},$$
--   equivalently the set of $z$ for which some $A\subseteq[n]$ with $|A|\ge n-e$ has $r(z)|_A\in C|_A$ and $[u_0,\dots,u_\ell]|_A\notin C^{\ell+1}|_A$.
--
--   For the one-point AG code $C=C_L(D,G)$ a codeword is $f(D)$ with $f\in L(G)$, so this is the set $S$ of Theorem 4.1.
--
--   **Formalization Note** $A$ ranges over all subsets of size at least $n-e$ (natural subtraction, so for $e\ge n$ every subset qualifies, as in the paper).
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Definition 2.4, p.14; Theorem 4.1, p.23

import Mathlib
import Definitions.Def_AGProxGap_curve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Classical

namespace AGProxGap.Supplement

/-- **The set of parameters with an MCA-bad agreement witness** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), Definition 2.4, p.14:
"an e agreement witness is a triple (z, c, A) with z ∈ F_q, c ∈ C, A ⊆ [n], |A| ≥ n − e and
c|_A = r(z)|_A. It is MCA-bad if no c_0, . . . , c_ℓ ∈ C satisfy c_j|_A = u_j|_A for every
0 ≤ j ≤ ℓ"; Theorem 4.1, p.23: "Let S ⊆ F_q be the set of parameters z for which there exist
f ∈ L(G) and A ⊆ [n] such that (z, f, A) is an MCA-bad e agreement witness").

For a code `C ⊆ K^n`, words `u_0, …, u_ℓ` and a radius `e`, the set consists of the `z ∈ K`
for which some `A ⊆ [n]` with `|A| ≥ n − e` satisfies:
1. some codeword `c ∈ C` agrees with `r(z) = Σ_j z^j u_j` on `A` (`r(z)|_A ∈ C|_A`), and
2. no codewords `c_0, …, c_ℓ ∈ C` agree with `u_0, …, u_ℓ` on that same `A`
   (`[u_0, …, u_ℓ]|_A ∉ C^{ℓ+1}|_A`).

**Formalization Note** `A` ranges over all `Finset (Fin n)` of size at least `n − e` (natural
subtraction; for `e ≥ n` the size condition is empty, as in the paper). The words are indexed by
`Fin (ℓ + 1)` and the curve is the base `AGProxGap.curve`. For the one-point AG code
`C = agCode P Pinf m`, "`c ∈ C`" is "`c = f(D)` for some `f ∈ L(G)`", so this is the paper's set
`S` of Theorem 4.1 (p.15: the witness is MCA-bad if no `v_0, …, v_ℓ ∈ L(G)` have
`v_j(P_i) = u_{j,i}` for `i ∈ A`). -/
noncomputable def mcaBadSet {K : Type*} [Field K] [Fintype K] {n ℓ : ℕ} (C : Set (Fin n → K))
    (u : Fin (ℓ + 1) → Fin n → K) (e : ℕ) : Finset K :=
  Finset.univ.filter (fun z => ∃ A : Finset (Fin n), n - e ≤ A.card ∧
    (∃ c ∈ C, ∀ i ∈ A, c i = curve u z i) ∧
    ¬ ∃ c : Fin (ℓ + 1) → Fin n → K, (∀ j, c j ∈ C) ∧ ∀ j, ∀ i ∈ A, c j i = u j i)

end AGProxGap.Supplement


