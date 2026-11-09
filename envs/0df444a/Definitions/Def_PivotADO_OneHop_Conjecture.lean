-- Prove2me | Definitions.Def_PivotADO_OneHop_Conjecture
-- name    : PivotADO_OneHop_Conjecture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:49.161453+00:00
-- url     : https://prove2.me/theorems/fa83750b-1182-490f-9659-ee3798ced038
-- title:
--   Conjecture 1 — the constant-degree girth conjecture
-- statement:
--   The constant-degree girth conjecture asserts that there are an integer $d\ge3$ and a real $C\ge0$ such that, for every size threshold $N$, there are $n\ge N$ and a $d$-regular graph $G$ on $n$ vertices with finite girth $g$ satisfying
--
--   $$g\ge 2\log_{d-1}n-C.$$
--
--   Both constants precede $N,n,G$. Vertices are represented by $\mathrm{Fin}(n)$ and finite girth by equality of extended girth to $g$. This is an open conjecture, encoded as a proposition for use as a hypothesis; no axiom or proof is supplied.
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Conjecture 1, p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Geometry

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop

/-- Conjecture 1, Kadria–Roditty, STOC 2027 submission #584 (October 2026), p.6.
This is an open hypothesis, not an axiom or an asserted existence theorem. -/
def ConstantDegreeGirthConjecture : Prop :=
  ∃ (d : ℕ) (C : ℝ), 3 ≤ d ∧ 0 ≤ C ∧
    ∀ N : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (g : ℕ),
      N ≤ n ∧ G.IsRegularOfDegree d ∧ G.egirth = (g : ℕ∞) ∧
        2 * Real.logb ((d : ℝ) - 1) (n : ℝ) - C ≤ (g : ℝ)

end PivotADO.OneHop


