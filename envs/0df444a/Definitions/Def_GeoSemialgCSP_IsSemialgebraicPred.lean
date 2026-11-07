-- Prove2me | Definitions.Def_GeoSemialgCSP_IsSemialgebraicPred
-- name    : GeoSemialgCSP_IsSemialgebraicPred
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:40.583205+00:00
-- url     : https://prove2.me/theorems/3f8b8e66-a750-412e-b2f6-dedd073a92ec
-- title:
--   Semialgebraic predicate on $(\mathbb R^d)^k$
-- statement:
--   A $k$-ary predicate $P:(\mathbb R^d)^k\to\{0,1\}$ is **semialgebraic** if its set of satisfying tuples $S=P^{-1}(1)$ is a semialgebraic subset of $\mathbb R^{kd}$, the space of the $k\cdot d$ coordinates of the $k$ points: it is defined by a Boolean combination of polynomial equalities and inequalities in these coordinates. Equivalently, $S$ is a finite union of basic sets $\{v: p_1(v)=\dots=p_r(v)=0,\ g_1(v)<0,\dots,g_s(v)<0\}$ with real polynomials $p_i,g_j$.
--
--   Semialgebraic predicates encode distance comparisons, orientations, orderings and finite-domain constraints; they are the predicates of the CSPs studied in the paper.
--
--   **Formalization Note** The predicate is its accepting set $S$. Point $j$, coordinate $i$ is coordinate `finProdFinEquiv (j, i)` of $\mathbb R^{kd}$. Semialgebraicity is the published normal form `NonconvexSplitting.ADMMKL.IsSemialgebraicSet`.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §1 p.1 and §3 'Semialgebraic sets', p.8 (PDF pp.2, 9)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_NonconvexSplitting_ADMMKL_Semialgebraic

namespace GeoSemialgCSP

/-- **Semialgebraic predicate.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §1 p.1 and §3 "Semialgebraic sets",
printed p.8 (PDF p.9): a set is semialgebraic if it is defined by a Boolean combination of polynomial
equalities and inequalities; a `k`-ary predicate on `ℝ^d` is semialgebraic if its accepting set is
semialgebraic in the `k·d` coordinates of the participating points.

**Formalization Note.** A predicate `P : (ℝ^d)^k → {0,1}` is its accepting set `S`. The `k` points
are concatenated through `finProdFinEquiv : Fin k × Fin d ≃ Fin (k*d)` (point `j`, coordinate `i`
is coordinate `finProdFinEquiv (j, i)`). Semialgebraicity is the published
`NonconvexSplitting.ADMMKL.IsSemialgebraicSet` (finite union of basic sets `p = 0, g < 0`), which
is the normal form of a Boolean combination of polynomial equalities and inequalities. -/
def IsSemialgebraicPred {k d : ℕ} (S : Set (Fin k → E d)) : Prop :=
  NonconvexSplitting.ADMMKL.IsSemialgebraicSet
    {v : Fin (k * d) → ℝ |
      (fun j : Fin k => (WithLp.toLp 2 (fun i : Fin d => v (finProdFinEquiv (j, i))) : E d)) ∈ S}

end GeoSemialgCSP


