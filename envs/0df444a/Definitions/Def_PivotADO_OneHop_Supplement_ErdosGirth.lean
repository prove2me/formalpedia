-- Prove2me | Definitions.Def_PivotADO_OneHop_Supplement_ErdosGirth
-- name    : PivotADO_OneHop_Supplement_ErdosGirth
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:55:48.938184+00:00
-- url     : https://prove2.me/theorems/ab7b73b8-87e2-4d98-826e-50926d824255
-- title:
--   The standard Erdős girth conjecture (girth $\ge 2t+2$ with $\Omega(N^{1+1/t})$ edges)
-- statement:
--   The **standard Erdős girth conjecture** states that for every integer $t\ge1$ there are graphs with girth at least $2t+2$ and $\Omega(N^{1+1/t})$ edges, where $N$ is the number of vertices. It is encoded as: for every integer $t\ge1$ there is a constant $a>0$ such that for every threshold $N_0$ there are $N\ge N_0$ and a simple graph $B$ on $N$ vertices with
--
--   $$\operatorname{girth}(B)\ge 2t+2\qquad\text{and}\qquad |E(B)|\ge a\,N^{1+1/t}.$$
--
--   By the Moore bound, a graph of girth at least $2t+2$ has $O(N^{1+1/t})$ edges, so the conjectured count matches the Moore bound up to a constant factor. This conjecture is the hypothesis of the hopset lower bounds (Theorems 3 and 4). It differs from the constant-degree conjecture (Conjecture 1): it asks for no regularity, no bounded degree and no logarithmic girth.
--
--   **Formalization Note** This is an open conjecture, defined as a proposition to be used as a hypothesis; no axiom or proof is supplied. Vertices are $\mathrm{Fin}(N)$; girth is Mathlib's extended girth `egirth`, which is $\infty$ for acyclic graphs. The constant $a$ depends only on $t$ and is chosen before $N$; graphs are required only for arbitrarily large $N$, the weakest reading of the $\Omega$-family.
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), §6 introduction, p.24 (PDF p. 25), and Remark 3, p.31 (PDF p. 32); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Geometry

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop.Supplement

open PivotADO.OneHop

/-- The standard Erdős girth conjecture, as stated in Kadria–Roditty, STOC 2027 submission
#584 (October 2026), §6, p.24 (PDF 25) and Remark 3, p.31 (PDF 32): for every integer
`t ≥ 1` there are graphs of girth at least `2t + 2` with `Ω(N^{1+1/t})` edges. The
constant `a` depends only on `t` and precedes `N`; graphs are required for arbitrarily
large `N`. An acyclic graph has girth `⊤`. This is an open hypothesis, not an axiom. -/
def ErdosGirthConjecture : Prop :=
  ∀ t : ℕ, 1 ≤ t → ∃ a : ℝ, 0 < a ∧
    ∀ N₀ : ℕ, ∃ (N : ℕ) (B : SimpleGraph (Fin N)),
      N₀ ≤ N ∧ ((2 * t + 2 : ℕ) : ℕ∞) ≤ B.egirth ∧
        a * (N : ℝ) ^ (1 + 1 / (t : ℝ)) ≤ (edgeCount B : ℝ)

end PivotADO.OneHop.Supplement


