-- Prove2me | Definitions.Def_NumberField_IsSplitPrime
-- name    : NumberField_IsSplitPrime
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/7ffc4993-96e1-5b9d-8602-aaa0ba72cf3f
-- title:
--   Completely split degree-one primes of a number field extension
-- statement:
--   Fix number fields $K$ and $M$ with $M$ a Galois extension of $K$. For an ideal $\mathfrak{l}$ of the ring of integers $\mathcal{O}_K$, the predicate [`NumberField.IsSplitPrime K M 𝔩`](../def/NumberField_IsSplitPrime.html#L13) is the conjunction of three conditions. First, $\mathfrak{l}$ is a maximal ideal of $\mathcal{O}_K$. Second, the absolute norm $\operatorname{absNorm} \mathfrak{l}$, i.e. the cardinality of $\mathcal{O}_K/\mathfrak{l}$ as a natural number, is a prime number; together with maximality this says exactly that $\mathfrak{l}$ is a prime of $K$ of residue degree one over $\mathbb{Q}$, with residue field $\mathbb{F}_\ell$ for $\ell = \operatorname{absNorm} \mathfrak{l}$. Third, the number of primes of $\mathcal{O}_M$ lying over $\mathfrak{l}$, measured as the `Nat.card` of Mathlib's set `𝔩.primesOver (𝓞 M)` of maximal ideals of $\mathcal{O}_M$ above $\mathfrak{l}$, equals $\operatorname{finrank}_K M = [M:K]$.
--
--   The third clause is thus phrased as a counting condition on the fibre of $\operatorname{Spec} \mathcal{O}_M \to \operatorname{Spec} \mathcal{O}_K$ over $\mathfrak{l}$, not as the assertion that all ramification indices and residue degrees equal one; in the Galois situation the two are equivalent, since $efg = [M:K]$ forces $e = f = 1$ precisely when $g = [M:K]$. So `IsSplitPrime K M 𝔩` holds exactly for those degree-one primes of $K$ which split completely in $M$; its negation, imposed alongside the first two clauses, singles out the degree-one primes of $K$ that are not completely split in $M$.
--
--   **Relation to Mathlib.** The ingredients — `Ideal.IsMaximal`, `Ideal.absNorm` and `Ideal.primesOver` — are Mathlib's; the packaged predicate combining "degree one over $\mathbb{Q}$" with "completely split in $M$" is this development's own.
--
--   **Where it is used.** The predicate organises the prime-density input to the class-field-theory-free treatment of a vanishing statement for a certain extension group: one bounds the Dirichlet density of the completely split degree-one primes by $1/[M:K]$, and shows that the remaining (non-split) degree-one primes generate the class group of $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_IsSplitPrime.lean

import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.RamificationInertia.Galois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace NumberField

open scoped NumberField nonZeroDivisors

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

def IsSplitPrime (𝔩 : Ideal (𝓞 K)) : Prop :=
  𝔩.IsMaximal ∧ (Ideal.absNorm 𝔩).Prime ∧
    Nat.card (𝔩.primesOver (𝓞 M)) = Module.finrank K M

end NumberField


