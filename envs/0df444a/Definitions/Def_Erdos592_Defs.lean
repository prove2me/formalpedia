-- Prove2me | Definitions.Def_Erdos592_Defs
-- name    : Erdos592_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T18:00:53.675333+00:00
-- url     : https://prove2.me/theorems/da6b5758-f9ae-431d-904b-c2d60c50d0f9
-- title:
--   Ordinal Ramsey property $\alpha\to(\beta,c)^2$ and sums of $k$ indecomposable ordinals
-- statement:
--   This file introduces the two notions in which the Erdős Problem 592 mission is stated.
--
--   1. **The ordinal Ramsey property** $\alpha \to (\beta, c)^2$. Let $\alpha,\beta$ be ordinals and $c$ a cardinal. Identify $\alpha$ with a well-ordered set of order type $\alpha$, and consider the complete graph $K_\alpha$ on it. We say $\alpha \to (\beta, c)^2$ if for every colouring of the edges of $K_\alpha$ in red and blue (every pair of distinct vertices receives exactly one colour), at least one of the following holds:
--      - there is a set $S$ of vertices, all of whose pairs are red, such that $S$ with the induced order has order type exactly $\beta$ (a *red $K_\beta$*); or
--      - there is a set $T$ of vertices, all of whose pairs are blue, with $|T| = c$ (a *blue $K_c$*).
--
--      An ordinal $\alpha$ with $\alpha \to (\alpha, 3)^2$ is called a **partition ordinal**.
--
--   2. **Sums of $k$ indecomposable ordinals.** An ordinal is *additively indecomposable* when it has the form $\omega^{\delta}$. For $k\in\mathbb N$, we say $\gamma$ is **the sum of $k$ indecomposable ordinals** if
--   $$
--   \gamma = \omega^{\delta_1} + \omega^{\delta_2} + \cdots + \omega^{\delta_k}, \qquad \delta_1 \ge \delta_2 \ge \cdots \ge \delta_k .
--   $$
--   Equivalently, the Cantor normal form of $\gamma$ has exactly $k$ terms when coefficients are counted with multiplicity (for example $\omega\cdot 2 = \omega+\omega$ is a sum of two, and $\omega^2+\omega+1$ is a sum of three).
--
--   These notions are used to state the known results of Specker, Chang, Galvin–Larson and Schipperus, and the remaining open case of the problem.
--
--   **Formalization Note** The graph lives on the canonical well-ordered type of order type $\alpha$; a red/blue colouring is a pair of complementary simple graphs. "Order type exactly $\beta$" is the order type of the subset with the inherited order. The non-increasing requirement on the exponents is what makes "sum of exactly $k$" well defined (without it, $\omega+\omega^2=\omega^2$ would count as a sum of two).
-- source:
--   T. F. Bloom, Erdős Problem #592, https://www.erdosproblems.com/592 (page last edited 23 January 2026); Lean encoding of the ordinal Ramsey property follows Formal Conjectures, FormalConjecturesForMathlib/SetTheory/Cardinal/SimpleGraph.lean and FormalConjectures/ErdosProblems/592.lean, https://github.com/google-deepmind/formal-conjectures

import Mathlib

open Cardinal Ordinal

universe u

namespace Erdos592

/-- The ordinal Ramsey property `α → (β, c)²`: for every red/blue colouring of the edges of the
complete graph on (the well-order of type) `α`, there is a red clique of order type `β` or a blue
clique of cardinality `c`. -/
def OrdinalCardinalRamsey (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
    ∃ s, blue.IsClique s ∧ #s = c

/-- `γ` is the sum of exactly `k` additively indecomposable ordinals, written in non-increasing
order: `γ = ω^δ₁ + ⋯ + ω^δₖ` with `δ₁ ≥ ⋯ ≥ δₖ` (i.e. the Cantor normal form of `γ` has exactly
`k` terms, counted with multiplicity). -/
def IsSumOfIndecomposables (k : ℕ) (γ : Ordinal.{u}) : Prop :=
  ∃ l : List Ordinal.{u}, l.length = k ∧ l.Pairwise (· ≥ ·) ∧ γ = (l.map (ω ^ ·)).sum

end Erdos592


