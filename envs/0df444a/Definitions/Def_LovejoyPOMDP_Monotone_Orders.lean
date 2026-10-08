-- Prove2me | Definitions.Def_LovejoyPOMDP_Monotone_Orders
-- name    : LovejoyPOMDP_Monotone_Orders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:24:56.296492+00:00
-- url     : https://prove2.me/theorems/1b374c3c-1922-44f2-aebb-8fb646bbadc0
-- title:
--   §1 — the simplex Π(X), first-order stochastic dominance ≥s, the MLR order ≥r, the strong MLR order ≥tp and TP₂
-- statement:
--   Let $X$ be a finite, completely ordered set with $n$ elements, and let
--   $$\Pi(X)=\Big\{\pi\in\mathbb R^{X} : \pi_i\ge 0 \text{ for all } i,\ \sum_{i\in X}\pi_i=1\Big\}$$
--   be the set of probability mass functions on $X$. For vectors $\pi,\pi'$ indexed by $X$:
--
--   1. **First-order stochastic dominance.** $\pi\ge_s\pi'$ if every upper tail sum of $\pi$ is at least that of $\pi'$:
--   $$\sum_{i\ge q}\pi_i\ \ge\ \sum_{i\ge q}\pi'_i\qquad\text{for every } q\in X.$$
--   2. **Monotone likelihood ratio (MLR) order.** $\pi\ge_r\pi'$ if $i\ge i'$ in $X$ implies $\pi_i\pi'_{i'}\ge\pi_{i'}\pi'_i$.
--   3. **Strong MLR order.** For two finite chains $X, Y$ and functions $f,g:X\times Y\to\mathbb R$, $f\ge_{tp} g$ if
--   $$f(x\vee x',\,y\vee y')\,g(x\wedge x',\,y\wedge y')\ \ge\ f(x,y)\,g(x',y')\qquad\text{for all }(x,y),(x',y')\in X\times Y,$$
--   where $\vee=\max$ and $\wedge=\min$. The relation $\ge_{tp}$ is not reflexive in general.
--   4. **Total positivity of order 2.** $f$ is $\mathrm{TP}_2$ if $f\ge_{tp} f$.
--   5. **Maximizer sets.** For a real function $f$ on a set $A$, $\operatorname{argmax} f=\{a\in A : f(b)\le f(a) \text{ for all } b\in A\}$.
--
--   These are the orders in which Lovejoy's monotonicity results for partially observed Markov decision processes are stated: $\ge_s$ is the familiar first-order stochastic dominance, $\ge_r$ is the stronger likelihood-ratio order that survives Bayesian conditioning, and $\ge_{tp}$ compares transition matrices of different actions.
--
--   **Formalization Note** $X$ is any type with `[Fintype X] [LinearOrder X]` (every finite chain is order-isomorphic to $\{1,\dots,n\}$), and $\Pi(X)$ is Mathlib's `stdSimplex ℝ X`. The orders are plain relations on all of $X\to\mathbb R$, with the larger vector as first argument: `StochGE π π'` is $\pi\ge_s\pi'$, `MLRGE π π'` is $\pi\ge_r\pi'$, `TPGE f g` is $f\ge_{tp} g$ for curried $f,g : X\to Y\to\mathbb R$. They are not `LE` instances. Theorems using them state simplex membership as a hypothesis.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, pp. 736–737, §1 (definitions of Π(X), ≥s, ≥r, ≥tp, TP2); p. 741 (argmax, in the definition of α(π))

import Mathlib

namespace LovejoyPOMDP.Monotone

/-! # §1 of Lovejoy (1987): orders on probability vectors of a finite chain

Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*,
Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, §1, pp. 736–737.

**Formalization Note.** The paper's finite, completely ordered set `X = {1, …, n}` with its natural
order is a type `X` with `[Fintype X] [LinearOrder X]`; every finite chain is order-isomorphic to
`{1, …, n}`. The set `Π(X)` of probability mass functions on `X` is Mathlib's `stdSimplex ℝ X`.
The orders are plain relations on `X → ℝ`, never `LE` instances (that would clash with the
pointwise order). In every relation the *larger* vector comes first: `StochGE π π'` is
`π ≥s π'`, `MLRGE π π'` is `π ≥r π'`, `TPGE f g` is `f ≥tp g`. The relations are defined on all
of `X → ℝ`; the paper uses them on `Π(X)` only, and every theorem of the mission states simplex
membership as a hypothesis. -/

/-- First-order stochastic dominance `π ≥s π'` (§1, p. 736, (i)): for every `q ∈ X`,
`Σ_{i ≥ q} π_i ≥ Σ_{i ≥ q} π'_i` (upper tail sums). -/
def StochGE {X : Type*} [Fintype X] [LinearOrder X] (π π' : X → ℝ) : Prop :=
  ∀ q : X, ∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π' i ≤
    ∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π i

/-- The monotone likelihood ratio order `π ≥r π'` (§1, p. 736, (ii)): `i ≥ i'` in `X` implies
`π_i π'_{i'} ≥ π_{i'} π'_i`. -/
def MLRGE {X : Type*} [LinearOrder X] (π π' : X → ℝ) : Prop :=
  ∀ i i' : X, i' ≤ i → π i' * π' i ≤ π i * π' i'

/-- The strong MLR order `f ≥tp g` on functions `X × Y → ℝ` (§1, p. 737), written curried:
`f(x ∨ x', y ∨ y') g(x ∧ x', y ∧ y') ≥ f(x, y) g(x', y')` for **all** `(x, y), (x', y')` in
`X × Y`, where `∨ = max` and `∧ = min` on each chain. For a matrix `P` with entries `P i j`,
this is the paper's `P ≥tp P'` with `f = P`, `g = P'`. -/
def TPGE {X Y : Type*} [LinearOrder X] [LinearOrder Y] (f g : X → Y → ℝ) : Prop :=
  ∀ (x : X) (y : Y) (x' : X) (y' : Y),
    f x y * g x' y' ≤ f (max x x') (max y y') * g (min x x') (min y y')

/-- `f` is TP₂ (totally positive of order 2) if `f ≥tp f` (§1, p. 737). -/
def TP2 {X Y : Type*} [LinearOrder X] [LinearOrder Y] (f : X → Y → ℝ) : Prop :=
  TPGE f f

/-- The set of maximizers of a real function on a type: `argmax f = {a | f b ≤ f a for all b}`.
Used for the maximizer sets `A*`, `A'*` of Lemma 2.2, the optimal actions `δ*_t(π)`, `δ*(π)`
and the myopic actions `α(π)` (pp. 738, 741). -/
def argmaxSet {A : Type*} (f : A → ℝ) : Set A :=
  {a | ∀ b, f b ≤ f a}

end LovejoyPOMDP.Monotone


