-- Prove2me | Definitions.Def_TightCoreset2027_Euclidean_coresetModel
-- name    : TightCoreset2027_Euclidean_coresetModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:05:58.293175+00:00
-- url     : https://prove2.me/theorems/69132779-75f5-4834-8779-0b9f1240b718
-- title:
--   Finite clustering costs and strong subset coresets
-- statement:
--   Let $X$ be a finite set in a metric space and let $C$ be a nonempty finite set of centers. The nearest-center distance and unweighted clustering cost, for a real exponent $z$, are
--
--   $$d(p,C)=\min_{c\in C}d(p,c),\qquad \operatorname{cost}_z(X,C)=\sum_{p\in X}d(p,C)^z.$$
--
--   For a finite candidate $S$ with arbitrary nonnegative weights $w$, put $\operatorname{cost}_z(S,w,C)=\sum_{p\in S}w(p)d(p,C)^z$. A strong coreset satisfies $S\subseteq X$ and
--
--   $$|\operatorname{cost}_z(S,w,C)-\operatorname{cost}_z(X,C)|\le\varepsilon\operatorname{cost}_z(X,C)\quad\text{for every ambient }C\text{ with }|C|=k.$$
--
--   The Euclidean point type is $\mathbb R^d$ with its Euclidean norm. The helper $\operatorname{lowerBoundScale}(z,k,\varepsilon)$ is $\min\{k^{(2z+2)/(z+2)}\varepsilon^{-2},k\varepsilon^{-z-2}\}$. This model supplies the goal's objective independently of the lower-bound construction.
--
--   **Formalization Note** Finite sets count distinct locations. Weights are ambient nonnegative real functions whose values outside $S$ are ignored; every function on $S$ extends by zero. The empty candidate and zero weights are allowed. Empty-query distance is defined as zero solely to totalize the helper; all results use $k\ge1$ and exactly $k$ centers. Real powers, rather than integer powers, define the objective. The paper's valid exponent and accuracy domains are imposed by the theorem using the predicate.
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), Definition 1.1 and footnote 1, printed p. 1 / PDF p. 3; Theorem 1.2, printed p. 3 / PDF p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Mathlib
open scoped BigOperators
set_option autoImplicit false

namespace TightCoreset2027.Euclidean

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Finite nearest-center distance; the empty-query value is unused when k ≥ 1. -/
noncomputable def nearestDistance {E : Type*} [PseudoMetricSpace E]
    (p : E) (C : Finset E) : ℝ := by
  classical
  exact if h : C.Nonempty then C.inf' h (fun c => dist p c) else 0

noncomputable def cost {E : Type*} [PseudoMetricSpace E]
    (z : ℝ) (X C : Finset E) : ℝ :=
  ∑ p ∈ X, Real.rpow (nearestDistance p C) z

noncomputable def weightedCost {E : Type*} [PseudoMetricSpace E]
    (z : ℝ) (S : Finset E) (w : E → NNReal) (C : Finset E) : ℝ :=
  ∑ p ∈ S, (w p : ℝ) * Real.rpow (nearestDistance p C) z

/-- Definition 1.1: all ambient queries of exactly k distinct centers. -/
def IsStrongCoreset {E : Type*} [PseudoMetricSpace E]
    (z ε : ℝ) (k : ℕ) (X S : Finset E) (w : E → NNReal) : Prop :=
  S ⊆ X ∧ ∀ C : Finset E, C.card = k →
    |weightedCost z S w C - cost z X C| ≤ ε * cost z X C

/-- The two branches of Theorem 1.2 before the polylogarithmic factor. -/
noncomputable def lowerBoundScale (z : ℝ) (k : ℕ) (ε : ℝ) : ℝ :=
  min (Real.rpow (k : ℝ) ((2 * z + 2) / (z + 2)) * Real.rpow ε (-2))
    ((k : ℝ) * Real.rpow ε (-z - 2))

end TightCoreset2027.Euclidean


