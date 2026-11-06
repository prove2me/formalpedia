-- Prove2me | Definitions.Def_BinaryQueryLB_Solves
-- name    : BinaryQueryLB_Solves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:40.011766+00:00
-- url     : https://prove2.me/theorems/422a334c-1a78-4133-9f00-fbd3eb714c2f
-- title:
--   The algorithm outputs an $\varepsilon$-optimal point for every function of a set
-- statement:
--   Given a chart $G$, a set $S$ of functions and $\varepsilon>0$, the algorithm $A$ **outputs an $\varepsilon$-optimal point for every $f\in S$ under $G$** if, for every $f\in S$, its run on $(f,G)$ stops after some number $T$ of queries with an output $\hat y$ that is $\varepsilon$-optimal for $f$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_BinaryQueryLB_StopsWith
import Definitions.Def_BinaryQueryLB_IsEpsOptimal

namespace BinaryQueryLB

/-- **The algorithm outputs an ε-optimal point for every function of a set.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Theorem 1.1,
p.4: "every deterministic algorithm with local binary queries that, under `Gcan`, outputs an
ε-optimal point for every `f ∈ F(d, R, M)`".

`Solves d R G S ε A`: for every `f ∈ S`, the run of `A` on `(f, G)` stops after some number `T` of
queries with an output `ŷ` that is ε-optimal for `f`. -/
def Solves (d : ℕ) (R : ℝ) (G : Chart d) (S : Set (EuclideanSpace ℝ (Fin d) → ℝ)) (ε : ℝ)
    (A : Algorithm d) : Prop :=
  ∀ f ∈ S, ∃ (T : ℕ) (yh : EuclideanSpace ℝ (Fin d)), StopsWith A G f T yh ∧ IsEpsOptimal d R f ε yh

end BinaryQueryLB


