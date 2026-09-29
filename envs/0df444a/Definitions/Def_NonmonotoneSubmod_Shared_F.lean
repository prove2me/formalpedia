-- Prove2me | Definitions.Def_NonmonotoneSubmod_Shared_F
-- name    : NonmonotoneSubmod_Shared_F
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:57:56.483304+00:00
-- url     : https://prove2.me/theorems/cce62286-a820-45e3-889a-4c4b76bbf7f3
-- title:
--   Expected value on an independently sampled random subset (multilinear extension)
-- statement:
--   Let $X$ be a finite ground set, $f : 2^X \to \mathbb{R}$, and $x \in \mathbb{R}^X$. For $x \in [0,1]^X$, let $\hat{x}$ be the random subset of $X$ that contains each element $i$ independently with probability $x_i$. The expectation of $f(\hat{x})$ is the finite sum
--
--   $$F(x) = \mathbf{E}[f(\hat{x})] = \sum_{S \subseteq X} f(S) \prod_{i \in S} x_i \prod_{i \notin S} (1 - x_i).$$
--
--   This is the **multilinear extension** of $f$. The random set $X(p)$ of the paper, in which every element is sampled independently with probability $p$, has $\mathbf{E}[f(X(p))] = F(p, \dots, p)$; in particular the uniformly random subset $R = X(1/2)$ of Algorithm RS has $\mathbf{E}[f(R)] = F(\tfrac12, \dots, \tfrac12) = 2^{-|X|} \sum_{S \subseteq X} f(S)$.
--
--   Used by three missions of this paper: 01-random-set (Algorithm RS and $X(p)$, p. 1137), 02-nonadaptive (the random set $R = X(1/2)$ and the marginal values $\omega(x)$ of Definition 2.4, p. 1138) and 04-smooth-local-search (the multilinear extension of §3.2 and the biased random sets $R(A, \delta)$ of Definition 3.5, p. 1142).
--
--   **Formalization Note** The formula is defined for every real vector $x$; it is an expectation only for $x \in [0,1]^X$, and every theorem that uses it as an expectation evaluates it at such an $x$. Expectations over random subsets are written throughout as these exact finite sums rather than as integrals against a probability measure.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1137, Algorithm RS (X(p)); p. 1142, §3.2 (multilinear extension F(x) = E[f(x̂)])

import Mathlib

namespace NonmonotoneSubmod.Shared

/-- The expectation of `f` on an independently sampled random subset (the multilinear extension,
Feige–Mirrokni–Vondrák 2011, p. 1142): element `i` is included independently with probability
`x i`, and `F f x = E[f(R)] = ∑_{S ⊆ X} f(S) ∏_{i ∈ S} x_i ∏_{i ∉ S} (1 - x_i)`.
The random set `X(p)` of p. 1137 corresponds to `x = fun _ => p`. -/
def F {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (x : X → ℝ) : ℝ :=
  ∑ S : Finset X, f S * ∏ i : X, (if i ∈ S then x i else 1 - x i)

end NonmonotoneSubmod.Shared


