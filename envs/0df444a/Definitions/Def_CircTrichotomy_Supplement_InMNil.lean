-- Prove2me | Definitions.Def_CircTrichotomy_Supplement_InMNil
-- name    : CircTrichotomy_Supplement_InMNil
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:13:54.530508+00:00
-- url     : https://prove2.me/theorems/b0fc7a9d-91d1-43c6-b78c-71f1758476ba
-- title:
--   The pseudovariety $\mathbf{MNil}$ of finite aperiodic monoids whose idempotents are central
-- statement:
--   $\mathbf{MNil}$ is the class of finite aperiodic monoids $M$ satisfying $ex=xe$ for all $x\in M$ and all idempotents $e\in E(M)$.
--
--   A semigroup $S$ is in $\mathbf{MNil}$ when
--
--   1. $S$ is finite;
--   2. $S$ has an identity element, so $S$ is a monoid;
--   3. $S$ is aperiodic: every $x\in S$ has $x^n=x^{n+1}$ for some $n\ge1$;
--   4. every idempotent $e$ ($e^2=e$) commutes with every element $x$: $ex=xe$.
--
--   Clause (4) of Theorem 5.1 asks for the syntactic semigroup of a neutral letter language to be in $\mathbf{MNil}$.
--
--   **Formalization Note** The identity element is part of the condition, not an assumption. For finite semigroups, "every subgroup is trivial", $x^\omega=x^{\omega+1}$ and $\exists n\ge1,\ x^n=x^{n+1}$ are equivalent; positive powers are written `spow x k` $=x^{k+1}$.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §B.5.1, p.40; §5, p.10

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

namespace Supplement

/-- Positive powers in a semigroup: `spow x k = x^(k+1)`. -/
def spow {S : Type} [Semigroup S] (x : S) : ℕ → S
  | 0 => x
  | k + 1 => spow x k * x

/-- **The pseudovariety `MNil`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular
Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §B.5.1, p.40):
"Let MNil denote the pseudovariety of finite aperiodic monoids M satisfying the identity ex = xe
for all elements x ∈ M and e ∈ E(M) [Str82]" (also §5, p.10: "the class of finite aperiodic
monoids whose idempotents commute with every element").

`InMNil S`: the semigroup `S` is finite, has an identity element (so it is a monoid), is aperiodic
(every `x` has `x^n = x^(n+1)` for some `n ≥ 1`), and every idempotent `e` (`e e = e`) commutes
with every element.

**Formalization Note** Membership of a semigroup in a pseudovariety of monoids means that it is a
monoid in it; the identity element is asserted, not assumed. For finite semigroups aperiodicity
(all subgroups trivial) is equivalent to `x^ω = x^(ω+1)` (the form used on p.40) and to
`∃ n ≥ 1, x^n = x^(n+1)`; powers are `spow x k = x^(k+1)`. -/
def InMNil (S : Type) [Semigroup S] : Prop :=
  Finite S ∧ (∃ one : S, ∀ x : S, one * x = x ∧ x * one = x) ∧
    (∀ x : S, ∃ k : ℕ, spow x k = spow x (k + 1)) ∧
    ∀ e x : S, e * e = e → e * x = x * e

end Supplement

end CircTrichotomy


