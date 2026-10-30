-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_IsBarycentricSpanner
-- name    : StochLinOpt_ConfBall2_IsBarycentricSpanner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:46:35.373609+00:00
-- url     : https://prove2.me/theorems/61e46e05-28c7-4fb5-abeb-a0dbb92a1f05
-- title:
--   Barycentric spanner of a decision set
-- statement:
--   Let $D\subset\mathbb R^n$. A family $b_1,\dots,b_n$ of vectors is a **barycentric spanner** for $D$ if
--
--   1. every $b_i$ lies in $D$, and
--   2. every $y\in D$ can be written as $y=\sum_{i=1}^n c_i\,b_i$ with all coefficients $c_i\in[-1,1]$.
--
--   Awerbuch and Kleinberg showed that every compact set has one. ConfidenceBall$_2$ uses the spanner to initialize its precision matrix, $A_1=\sum_i b_ib_i^\top$.
--
--   **Formalization Note** Vectors of $\mathbb R^n$ are functions `Fin n → ℝ`; the spanner is indexed by `Fin n`.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, §2 Preliminaries, unnumbered definition, p. 3

import Mathlib
open Matrix

namespace StochLinOpt.ConfBall2

/-- **Barycentric spanner** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, §2 Preliminaries, unnumbered definition, p. 3:
"A barycentric spanner for D is a set of vectors b1, . . . , bn, all contained in D, such that
every vector in D can be expressed as a linear combination of the spanner with coefficients in
[−1, 1]").

`IsBarycentricSpanner D b` holds when every `b i` lies in `D` and every `y ∈ D` is
`∑ i, c i • b i` with every `c i ∈ [−1, 1]`.

**Formalization Note** Vectors of `ℝⁿ` are `Fin n → ℝ`; the spanner is indexed by `Fin n`. -/
def IsBarycentricSpanner {n : ℕ} (D : Set (Fin n → ℝ)) (b : Fin n → Fin n → ℝ) : Prop :=
  (∀ i, b i ∈ D) ∧
    ∀ y ∈ D, ∃ c : Fin n → ℝ, (∀ i, c i ∈ Set.Icc (-1 : ℝ) 1) ∧ y = ∑ i, c i • b i

end StochLinOpt.ConfBall2


