-- Prove2me | Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
-- name    : BertsekasShreve_BorelInfinite_Analytic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:20:41.952643+00:00
-- url     : https://prove2.me/theorems/7b8711a5-154b-42e0-a44d-d56f4b2f3ef4
-- title:
--   Borel spaces, universally measurable sets and functions, lower semianalytic functions (Defs 7.7, 7.18, 7.20, 7.21)
-- statement:
--   This file fixes the descriptive-set-theoretic vocabulary of Chapter 7 that the infinite horizon Borel model uses.
--
--   1. **Borel space** (Definition 7.7). A topological space $X$ is a Borel space if it is homeomorphic to a Borel subset of a complete separable metric space.
--   2. **Universally measurable set** (Definition 7.18). For a probability measure $p$ on the Borel $\sigma$-algebra $\mathcal B_X$, let $\mathcal B_X(p)$ be the completion of $\mathcal B_X$ with respect to $p$. The universal $\sigma$-algebra is
--   $$\mathcal U_X = \bigcap_{p \in P(X)} \mathcal B_X(p),$$
--   and a set $E \in \mathcal U_X$ is called universally measurable.
--   3. **Universally measurable function** (Definition 7.20). A function $f : X \to Y$ into a measurable space $Y$ is universally measurable if $f^{-1}(B) \in \mathcal U_X$ for every Borel set $B \subseteq Y$.
--   4. **Lower semianalytic function** (Definition 7.21). Let $D \subseteq X$ and $f : D \to R^* = [-\infty, \infty]$. Then $f$ is lower semianalytic if $D$ is analytic and the set $\{x \in D \mid f(x) < c\}$ is analytic for every $c \in \mathbb R$. A function defined on all of $X$ is lower semianalytic if it is so with $D = X$.
--
--   These notions carry the measurability theory of the model: the one-stage cost is lower semianalytic, policies are universally measurable, and the optimal cost turns out to be lower semianalytic.
--
--   **Formalization Note** Analytic sets are Mathlib's `AnalyticSet`: the empty set or a continuous image of the Baire space $\mathbb N^{\mathbb N}$, which on a Borel space is the book's notion (Proposition 7.41). A set is universally measurable when it is null-measurable for every probability measure. The same vocabulary is drafted, under its own sub-namespace, by the series' mission on lower semianalytic functions; it is restated here because unpublished drafts cannot import one another.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 118, Definition 7.7; p. 167, Definition 7.18; p. 171, Definition 7.20; p. 177, Definition 7.21

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_AnalyticSelection_LowerSemianalytic
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability

namespace BertsekasShreve.BorelInfinite

open MeasureTheory

universe u

/-- **Definition 7.20** (p. 171), for a function defined on all of `X`: `f : X → Y` is
*universally measurable* if `f⁻¹(B)` is universally measurable for every Borel set `B ⊆ Y`. -/
def IsUniversallyMeasurableFun {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) : Prop :=
  ∀ B : Set Y, MeasurableSet B → BertsekasShreve.AnalyticSelection.IsUniversallyMeasurable (f ⁻¹' B)

/-- A function `f : X → R*` defined on all of `X` is lower semianalytic if it is so as a function
on `D = X` in the sense of Definition 7.21. -/
def IsLowerSemianalyticFun {X : Type*} [TopologicalSpace X] (f : X → EReal) : Prop :=
  BertsekasShreve.AnalyticSelection.IsLowerSemianalytic (Set.univ : Set X) (fun x => f x)

end BertsekasShreve.BorelInfinite


