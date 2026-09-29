-- Prove2me | Definitions.Def_Supermodularity_Matching_IsOptimalMatching
-- name    : Supermodularity_Matching_IsOptimalMatching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:18:59.052953+00:00
-- url     : https://prove2.me/theorems/b28c3876-e03e-4885-8bf5-a80641371e0f
-- title:
--   The matching problem (3.2.1) — an optimal matching
-- statement:
--   Fix $n$ worker types indexed $i = 1,\dots,n$, each with a lattice $X_i$ of available
--   worker qualities, and $m$ firms indexed $j = 1,\dots,m$. A **matching** assigns to each
--   firm $j$ a quality vector $x^j \in \prod_{i=1}^n X_i$ (one worker of each type), formalized
--   as a function $x : \mathrm{Fin}\,m \to \prod_i X_i$. If firm $j$ hires the vector of
--   qualities $x^j$, it earns profit $f(x^j, j) \in \mathbb{R}$.
--
--   A matching $x$ is **optimal** for the profit function $f$ if it maximizes the total profit
--   across all $m$ firms over every matching $y$:
--   $$\sum_{j=1}^m f(y^j, j) \;\le\; \sum_{j=1}^m f(x^j, j) \qquad \text{for every matching } y.$$
--
--   This is Topkis's matching problem (3.2.1): "a matching that maximizes the sum of the
--   profits for all the firms is optimal." Every candidate matching $y : \mathrm{Fin}\,m \to
--   \prod_i X_i$ is admissible in this maximization — the general model places no constraint
--   on $y$ beyond each $y^j$ lying in $\prod_i X_i$, since Topkis explains that the set
--   notation $\{x^1_i,\dots,x^m_i\}\subseteq X_i$ used to define "a matching" imposes no
--   further restriction once each $x^j_i$ already ranges over $X_i$ (p. 96: the representation
--   "may not distinguish between all distinct assignments of workers to firms if the qualities
--   of different workers of any given type are not all distinct, but that ambiguity is
--   inconsequential").
--
--   **Formalization Note.** A *tight* labor market (Definition, p. 96) restricts feasibility to
--   matchings that partition a fixed, finite supply of each worker type; that restriction is
--   formalized separately, as `IsTightMatching`, and appears as an extra hypothesis on the
--   matchings quantified over wherever the book's tight-market results need it — it is not
--   built into `IsOptimalMatching` itself, matching the book's general (not necessarily tight
--   or loose) definition of the matching problem (3.2.1).
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 97, Section 3.2, equation (3.2.1)

import Mathlib

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 97, Section 3.2, equation (3.2.1) (the matching problem) and the sentence "A matching that
maximizes the sum of the profits for all the firms is optimal."
-/

namespace Supermodularity.Matching

/-- `IsOptimalMatching f x` says the matching `x : Fin m → ∀ i, X i`, assigning to each of `m`
firms a vector of qualities of `n` worker types, is *optimal* for the profit function `f`: it
maximizes the total profit `∑ j, f (x j) j` over every matching `y : Fin m → ∀ i, X i`. -/
def IsOptimalMatching {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ) (x : Fin m → ∀ i, X i) : Prop :=
  ∀ y : Fin m → ∀ i, X i, ∑ j, f (y j) j ≤ ∑ j, f (x j) j

end Supermodularity.Matching


