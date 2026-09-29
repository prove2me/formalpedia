-- Prove2me | Definitions.Def_FormalHecke_Eigensystem
-- name    : FormalHecke_Eigensystem
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/17587369-4f63-52db-bc47-09e7b486841e
-- title:
--   Formal Hecke eigensystems: recursions for arithmetic functions
-- statement:
--   Both declarations are predicates on a pair of functions $e, a : \mathbb{N} \to R$ with $R$ a commutative ring; $e$ plays the role of the "Euler factor weights" (only its values at primes are used) and $a$ the role of a sequence of Fourier coefficients.
--
--   [`FormalHecke.IsEigensystem e a`](../def/FormalHecke_Eigensystem.html#L10) asserts two things: $a(1) = 1$, and for every prime $\ell$ and every natural number $n$,
--   $$a(\ell n) + e(\ell)\cdot\bigl[\ell \mid n\bigr]\,a(n/\ell) = a(\ell)\,a(n),$$
--   where the bracket denotes the term $a(n/\ell)$ when $\ell \mid n$ and $0$ otherwise, and $n/\ell$ is natural-number division. This is exactly the statement that the formal $q$-expansion with coefficients $a$ is an eigenvector of each formal operator $U_\ell + e(\ell)V_\ell$ with eigenvalue $a(\ell)$. Note that $n$ ranges over all of $\mathbb{N}$, including $n = 0$; since $\ell \mid 0$, the case $n = 0$ imposes the extra relation $\bigl(1 + e(\ell) - a(\ell)\bigr)a(0) = 0$ for every prime $\ell$.
--
--   [`FormalHecke.IsRecursive e a`](../def/FormalHecke_Eigensystem.html#L14) asserts the three conditions: $a(1) = 1$; $a(mn) = a(m)a(n)$ for all $m, n$ with $\gcd(m,n) = 1$ (multiplicativity spelled out directly, again with no positivity restriction on $m$, $n$); and the three-term recursion at prime powers, $a(\ell^{r+2}) = a(\ell)\,a(\ell^{r+1}) - e(\ell)\,a(\ell^{r})$ for every prime $\ell$ and every $r \ge 0$. The module contains only these two definitions; any equivalence between them is proved elsewhere, and neither predicate refers to modular forms, Hecke algebras or $q$-expansions — they are purely combinatorial conditions on the pair of sequences.
--
--   **Relation to Mathlib.** Mathlib has no notion of a formal Hecke eigensystem; these are the project's own predicates, stated for bare functions $\mathbb{N} \to R$ rather than through Mathlib's arithmetic-function API (multiplicativity over coprime arguments is written out inline).
--
--   **Where it is used.** The predicates give the bookkeeping used when coefficient systems are transported between modular forms of different weights and levels — with $e(\ell) = \ell^{k-1}$ at good primes and $e(\ell) = 0$ where only $U_\ell$ acts — in the congruence arguments leading to the existence of a weight-one newform. The module is imported by fourteen statement and proof modules of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FormalHecke_Eigensystem.lean

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace FormalHecke

variable {R : Type*} [CommRing R]

def IsEigensystem (e a : ℕ → R) : Prop :=
  a 1 = 1 ∧ ∀ ℓ : ℕ, ℓ.Prime → ∀ n : ℕ,
    a (ℓ * n) + e ℓ * (if ℓ ∣ n then a (n / ℓ) else 0) = a ℓ * a n

def IsRecursive (e a : ℕ → R) : Prop :=
  a 1 = 1 ∧ (∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n) ∧
    ∀ ℓ r : ℕ, ℓ.Prime → a (ℓ ^ (r + 2)) = a ℓ * a (ℓ ^ (r + 1)) - e ℓ * a (ℓ ^ r)

end FormalHecke


