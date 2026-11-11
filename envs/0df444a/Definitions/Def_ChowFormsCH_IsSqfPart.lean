-- Prove2me | Definitions.Def_ChowFormsCH_IsSqfPart
-- name    : ChowFormsCH_IsSqfPart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:56:28.642777+00:00
-- url     : https://prove2.me/theorems/f6ae0ecd-ef0a-4b25-94df-6065d50010ff
-- title:
--   Squarefree part, greatest common divisors, and uniform-sampling probability
-- statement:
--   In a commutative monoid with zero, $s$ is a **squarefree part** of $f$ if $f\neq 0$, $s$ is squarefree, $s\mid f$, and every prime factor of $f$ divides $s$; in a unique factorization domain this is the product of the distinct prime factors of $f$, up to a unit. An element $g$ is a **greatest common divisor** of $a$ and $b$ if it is a common divisor divisible by every common divisor, and of a set $S$ if it divides every element of $S$ and is divisible by every common divisor of $S$.
--
--   For a finite set $B$ and a predicate $P$ on vectors $a\in B^\iota$, the probability that $P$ holds when every coordinate of $a$ is picked independently and uniformly from $B$ is
--   $$
--   \Pr_{a\in B^\iota}[P(a)]=\frac{\#\{a\in B^\iota : P(a)\}}{|B|^{|\iota|}} .
--   $$
--
--   These are used in Lemmas 2.3, 2.13, 3.13, 4.6, 4.7, 4.8 and Theorem 4.9.
--
--   **Formalization Note** Squarefree parts and gcds are given as predicates, determined up to a unit; the paper's normalizations (monic gcd, p.8) only fix that unit.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), §2.1, p.8; Lemmas 4.6, 4.7, pp.31–32; Lemma 3.13, p.28

import Mathlib

set_option autoImplicit false

namespace ChowFormsCH

/-- `s` is a squarefree part of `f` (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric
computations in CH via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, Lemmas 4.2,
4.6, 4.7, pp.30–32): `f ≠ 0`, `s` is squarefree, `s` divides `f`, and every prime factor of `f`
divides `s`. In a unique factorization domain this determines `s` up to a unit: it is the product
of the distinct prime factors of `f`. -/
def IsSqfPart {R : Type*} [CommMonoidWithZero R] (f s : R) : Prop :=
  f ≠ 0 ∧ Squarefree s ∧ s ∣ f ∧ ∀ p : R, Prime p → p ∣ f → p ∣ s

/-- `g` is a greatest common divisor of `a` and `b`: a common divisor divisible by every common
divisor (§2.1, p.8; determined up to a unit, which is the only freedom the paper's statements
use). -/
def IsGcdOf {R : Type*} [CommMonoid R] (a b g : R) : Prop :=
  g ∣ a ∧ g ∣ b ∧ ∀ e : R, e ∣ a → e ∣ b → e ∣ g

/-- `g` is a greatest common divisor of all elements of `S` (Lemma 3.13, p.28: "the GCD of the
coefficients of P"). -/
def IsGcdOfSet {R : Type*} [CommMonoid R] (S : Set R) (g : R) : Prop :=
  (∀ a ∈ S, g ∣ a) ∧ ∀ e : R, (∀ a ∈ S, e ∣ a) → e ∣ g

open scoped Classical in
/-- The probability that `P` holds when every coordinate of `a : ι → α` is picked independently
and uniformly at random from the finite set `B`: the fraction `#{a ∈ B^ι : P a} / |B|^{|ι|}`
(used in Lemmas 2.3, 2.13, 4.7, 4.8 and Theorem 4.9). -/
noncomputable def unifProb {α ι : Type*} [Fintype ι] [DecidableEq ι] (B : Finset α)
    (P : (ι → α) → Prop) : ℝ :=
  (((Fintype.piFinset fun _ : ι => B).filter P).card : ℝ) / ((B.card : ℝ) ^ Fintype.card ι)

end ChowFormsCH


