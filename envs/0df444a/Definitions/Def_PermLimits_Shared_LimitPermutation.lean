-- Prove2me | Definitions.Def_PermLimits_Shared_LimitPermutation
-- name    : PermLimits_Shared_LimitPermutation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:55:25.838265+00:00
-- url     : https://prove2.me/theorems/b6558686-7111-4146-a30a-1ca7ef4e0fd8
-- title:
--   Cumulative distribution functions and limit permutations $\mathcal Z$
-- statement:
--   A function $F:[0,1]\to[0,1]$ is a **cdf** if $F$ is non-decreasing and right-continuous with $F(0)\ge 0$ and $F(1)=1$. Equivalently, $F(y)=\mathbf P(Y\le y)$ for some $[0,1]$-valued random variable $Y$.
--
--   A **limit permutation** is a Lebesgue measurable function $Z:[0,1]^2\to[0,1]$ such that
--
--   1. for every $x\in[0,1]$ the function $Z(x,\cdot)$ is a cdf, and
--   2. for every $y\in[0,1]$,
--   $$\int_0^1 Z(x,y)\,dx = y .$$
--
--   The set of limit permutations is denoted $\mathcal Z$. Heuristically $Z(x,\cdot)$ is the conditional cdf of $Y$ given $X=x$ for a random point $(X,Y)$ of the unit square with uniform marginals; condition 2 says that $Y$ is uniform. Limit permutations are the limit objects of convergent permutation sequences, as graphons are for dense graph sequences.
--
--   **Formalization Note** $[0,1]$ is Mathlib's `unitInterval` with Lebesgue measure. $Z$ is curried and real-valued, with values in $[0,1]$ as an explicit clause. "Lebesgue measurable" is almost-everywhere measurability of $(x,y)\mapsto Z(x,y)$ for the product Lebesgue measure on $[0,1]^2$, which is measurability for the completed σ-algebra. Conditions 1 and 2 hold for every $x$ and every $y$, not almost everywhere.
--
--   This definition is shared by both missions of this series: mission 1 (`01-limit-existence`, existence and uniqueness of the limit permutation) (Theorem 1.6, p. 4; Theorem 1.7, p. 5; Lemma 2.2 and Eq. (21), p. 9; Lemma 4.2, p. 13; Lemma 5.1, p. 15; Lemma 5.3, p. 16; Eq. (49), p. 17) and mission 2 (`02-cauchy-rectangular`, convergent sequences are Cauchy for the rectangular distance) (Theorem 1.6 (i), p. 4; Lemma 2.2 (a), p. 9; Eq. (34), p. 12; Lemma 5.3, p. 16; Eq. (49), p. 17).
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 3, Eq. (4) and Definition 1.3

import Mathlib

/-!
# Cumulative distribution functions and limit permutations

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2, p. 3, Eq. (4) and Definition 1.3.

A definition bundle: the cdf predicate (4) and the class `𝒵` of limit permutations.

**Formalization Note.** The unit interval `[0, 1]` is Mathlib's `unitInterval` (written `I`), a
subtype of `ℝ` carrying the restriction of Lebesgue measure as `volume` (a probability measure).
Values of `Z` are taken in `ℝ`, and membership in `[0, 1]` is a clause of the definition.
-/

namespace PermLimits.Shared

open MeasureTheory unitInterval

/-- **cdf** (Hoppen et al., arXiv:1103.5844v2, Eq. (4), p. 3). A function `F : [0,1] → [0,1]`
is a cdf if it is non-decreasing and right-continuous with `F(0) ≥ 0` and `F(1) = 1`.

**Formalization Note.** `F` is real-valued; its values lie in `[0, 1]` as a consequence of
monotonicity, `F(0) ≥ 0` and `F(1) = 1`. Right-continuity at `y` is continuity within `[y, 1]`.
-/
def IsCDF (F : I → ℝ) : Prop :=
  Monotone F ∧ (∀ y : I, ContinuousWithinAt F (Set.Ici y) y) ∧ 0 ≤ F 0 ∧ F 1 = 1

/-- **Limit permutation** (Hoppen et al., arXiv:1103.5844v2, Definition 1.3, p. 3). A limit
permutation is a Lebesgue measurable function `Z : [0,1]² → [0,1]` such that
(a) for **every** `x ∈ [0,1]`, `Z(x, ·)` is a cdf (Eq. (4)), and
(b) for **every** `y ∈ [0,1]`, `∫₀¹ Z(x, y) dx = y`.
The set of limit permutations is `𝒵`.

**Formalization Note.** `Z` is curried, `Z x y = Z(x, y)`. "Lebesgue measurable" is
`AEMeasurable (Function.uncurry Z)` for the product Lebesgue measure `volume` on `I × I`; a
real function is almost-everywhere measurable exactly when it is measurable for the completed
(Lebesgue) σ-algebra. Conditions (a) and (b) are imposed pointwise for every `x` and every `y`, as
in the paper, not almost everywhere. The integral in (b) is the Bochner integral over `I` with
respect to Lebesgue measure. -/
def IsLimitPerm (Z : I → I → ℝ) : Prop :=
  AEMeasurable (Function.uncurry Z) (volume : Measure (I × I)) ∧
  (∀ x y : I, Z x y ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ x : I, IsCDF (Z x)) ∧
  (∀ y : I, ∫ x, Z x y = (y : ℝ))

end PermLimits.Shared


