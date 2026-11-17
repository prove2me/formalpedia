-- Prove2me | Definitions.Def_BinaryQueryLB_Supplement_StrongSolvesEveryChart
-- name    : BinaryQueryLB_Supplement_StrongSolvesEveryChart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:52:32.976205+00:00
-- url     : https://prove2.me/theorems/e446bfcf-610e-473e-9882-5ee45bf4c8c7
-- title:
--   The $O^*$-algorithm is $\varepsilon$-accurate for every $f\in F(d,R,M)$ and every chart
-- statement:
--   An algorithm $A$ with $O^*$ is **$\varepsilon$-accurate for every function and every chart** if, for every first-order chart $G$ (a selection $G(f,y)\in\partial f(y)$ for $f\in F(d,R,M)$, $y\in X$) and every $f\in F(d,R,M)$, the run of $A$ on $(f,G)$ stops after finitely many queries with an output $\hat y$ that is $\varepsilon$-optimal for $f$, that is, $\hat y\in X$ and $f(\hat y)-\min_X f\le\varepsilon$.
--
--   Requiring success under every chart, rather than one fixed chart, lets the hard chart in a lower bound depend on the algorithm.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Theorem 1.4 and the paragraph before it, p.5

import Mathlib
import Definitions.Def_BinaryQueryLB_Supplement_StrongStopsWith
import Definitions.Def_BinaryQueryLB_IsChart
import Definitions.Def_BinaryQueryLB_IsEpsOptimal
import Definitions.Def_BinaryQueryLB_ProblemClass

namespace BinaryQueryLB.Supplement

/-- **The O\*-algorithm is ε-accurate for every function and every chart.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Theorem 1.4, p.5: "outputs a `(c0MR/√d)`-optimal point for every
`f ∈ F(d, R, M)` and every first-order chart"; p.5: "In this theorem the algorithm has to succeed for
every chart, so the hard chart may depend on the algorithm".

`StrongSolvesEveryChart d R M ε A`: for every first-order chart `G` (`IsChart d R M G`,
Definition 2.2) and every `f ∈ F(d, R, M)`, the run of `A` on `(f, G)` stops after some number
`T` of queries with an output `ŷ` that is ε-optimal for `f` (in particular `ŷ ∈ X`). -/
def StrongSolvesEveryChart (d : ℕ) (R M ε : ℝ) (A : StrongAlgorithm d) : Prop :=
  ∀ G : BinaryQueryLB.Chart d, BinaryQueryLB.IsChart d R M G →
    ∀ f ∈ BinaryQueryLB.ProblemClass d R M, ∃ (T : ℕ) (yh : EuclideanSpace ℝ (Fin d)),
      StrongStopsWith A G f T yh ∧ BinaryQueryLB.IsEpsOptimal d R f ε yh

end BinaryQueryLB.Supplement


