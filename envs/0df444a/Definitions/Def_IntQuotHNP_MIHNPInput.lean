-- Prove2me | Definitions.Def_IntQuotHNP_MIHNPInput
-- name    : IntQuotHNP_MIHNPInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:14.710146+00:00
-- url     : https://prove2.me/theorems/708c4ba0-7140-4cdc-95e7-72f16c7f4170
-- title:
--   Definition 4.1 — MIHNP inputs, the promise, consistency (4), and the solution set
-- statement:
--   A **public MIHNP input** consists of a modulus $p$, an error bound $X$, a number of samples $N$, shifts $t_1,\dots,t_N$ and approximations $v_1,\dots,v_N$. A pair $(y,x)$ of a secret and an error vector is **consistent** with the input when $y\in\mathbb Z_p=\{0,\dots,p-1\}$, every $x_i\in\{0,\dots,X-1\}$, and for every $i$
--   $$
--   (y+t_i)(v_i+x_i)\equiv 1\pmod p,\qquad v_i+x_i\in\mathbb Z_p .
--   $$
--   The input is **promised** when $p$ is prime, $3\le N<p$, $1\le X<p$, the shifts are pairwise distinct elements of $\mathbb Z_p$, each $v_i\in\mathbb Z_p$, and some consistent pair exists. The **solution set** is the set of all $y\in\mathbb Z_p$ for which some $x$ makes $(y,x)$ consistent; it is exactly what the recovery algorithm must return.
--
--   **Formalization Note** Residues are natural numbers below $p$. The paper's index $i\in\{1,\dots,N\}$ is the Lean index $i-1\in$ `Fin N`, so $t_1,v_1,x_1$ are `t 0`, `v 0`, `x 0`. The condition $v_i+x_i\in\mathbb Z_p$ is an integer inequality $v_i+x_i<p$; in `ZMod p` it would be lost and the solution set would grow.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 4.1 and (4), p.21 (PDF p.22); Theorem 4.2, p.22 (PDF p.23)

import Mathlib

namespace IntQuotHNP

/-- **A public MIHNP input** `(p, X, N, t, v)` (Definition 4.1).
Kang, Lee, *Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number
Problems*, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 4.1, p.21 (PDF p.22):
"The public input consists of distinct shifts t₁, . . . , t_N ∈ ℤ_p and approximations v ∈ ℤ_p^N."

The record holds the public parameters `p`, `X`, `N`, the shifts `t` and the approximations `v`.
Which records are genuine MIHNP inputs is the separate predicate `IsPromised`.

**Formalization Note.** Residues of `ℤ_p = {0, …, p − 1}` are natural numbers below `p`. The
paper's index `i ∈ [N] = {1, …, N}` is the Lean index `i − 1 ∈ Fin N`, so the paper's `t₁`, `v₁`,
`x₁` are `t 0`, `v 0`, `x 0`. -/
structure MIHNPInput where
  /-- the prime modulus `p` -/
  p : ℕ
  /-- the error bound `X` (errors lie in `{0, …, X − 1}`) -/
  X : ℕ
  /-- the number `N` of samples -/
  N : ℕ
  /-- the public shifts `t₁, …, t_N` -/
  t : Fin N → ℕ
  /-- the public approximations `v₁, …, v_N` -/
  v : Fin N → ℕ

/-- **A secret `y` and an error vector `x` consistent with an MIHNP input** (constraints (4)).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 4.1, p.21 (PDF p.22):
"Put B_i = {0, . . . , X − 1} for i ∈ [N] and B = ∏ B_i. … (y∗ + t_i)(v_i + x∗_i) ≡ 1 (mod p),
v_i + x∗_i ∈ ℤ_p (i ∈ [N]). (4)"

`Consistent I y x` says `y ∈ ℤ_p`, `x ∈ B`, and for every `i`: `v_i + x_i ∈ ℤ_p` and
`(y + t_i)(v_i + x_i) ≡ 1 (mod p)`.

**Formalization Note.** The condition `v_i + x_i ∈ ℤ_p` is an integer condition: since
`v_i, x_i ≥ 0` it is `v_i + x_i < p`. It is kept as an inequality of natural numbers; read in
`ZMod p` it would be lost. -/
def Consistent (I : MIHNPInput) (y : ℕ) (x : Fin I.N → ℕ) : Prop :=
  y < I.p ∧ ∀ i, x i < I.X ∧ I.v i + x i < I.p ∧ (y + I.t i) * (I.v i + x i) ≡ 1 [MOD I.p]

/-- **A promised MIHNP input** (Definition 4.1).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 4.1, p.21 (PDF p.22):
"Let p be prime and let N, X be integers with 3 ≤ N < p and 1 ≤ X < p. The public input consists
of distinct shifts t₁, . . . , t_N ∈ ℤ_p and approximations v ∈ ℤ_p^N. … The input is promised to
have a hidden secret y∗ ∈ ℤ_p and x∗ ∈ B such that (4)."

**Formalization Note.** Every clause of the definition is a conjunct: `p` prime, `3 ≤ N < p`,
`1 ≤ X < p`, shifts in `ℤ_p` and pairwise distinct, approximations in `ℤ_p`, and some consistent
pair `(y∗, x∗)`. The closing remark of Definition 4.1 on leading-bit observations (`X` a power of
two, `v_i ∈ Xℤ`) describes a special case and is not a condition. -/
def IsPromised (I : MIHNPInput) : Prop :=
  I.p.Prime ∧ 3 ≤ I.N ∧ I.N < I.p ∧ 1 ≤ I.X ∧ I.X < I.p ∧ (∀ i, I.t i < I.p) ∧
    Function.Injective I.t ∧ (∀ i, I.v i < I.p) ∧ ∃ y x, Consistent I y x

open Classical in
/-- **The secrets satisfying (4) with `x ∈ B`**: the exact output required of the algorithm.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 4.2, p.22 (PDF p.23):
"Algorithm 1 … deterministically returns exactly the secrets satisfying (4) with x ∈ B on every
promised input."

`solutionSet I = {y ∈ ℤ_p : ∃ x ∈ B, (y, x) satisfies (4)}`.

**Formalization Note.** A finite set of natural numbers below `p`. The error vector is
existentially quantified, so `y` counts once however many `x` fit it. -/
noncomputable def solutionSet (I : MIHNPInput) : Finset ℕ :=
  (Finset.range I.p).filter fun y => ∃ x : Fin I.N → ℕ, Consistent I y x

end IntQuotHNP


