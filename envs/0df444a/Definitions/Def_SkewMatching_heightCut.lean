-- Prove2me | Definitions.Def_SkewMatching_heightCut
-- name    : SkewMatching_heightCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:07:51.371489+00:00
-- url     : https://prove2.me/theorems/2471b39a-be7e-48de-ab80-172e402174ec
-- title:
--   Lemma 21 — the cut defined by vertex heights
-- statement:
--   For a directed graph $G_1$ with vertex heights $h$, the undirected graph $G_2$ has two copies $u^0,u^1$ of each vertex $u$, and two copies $(u^0,v^0)$, $(u^1,v^1)$ of each edge $(u,v)$. This definition is the vertex set
--
--   $$
--   S=\{u^0:h(u)\ge 0\}\cup\{u^1:h(u)\ge 1\}
--   $$
--
--   of $G_2$. It reduces sampling by height difference to sampling from a cut.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 21, p.13

import Mathlib

namespace SkewMatching

/-- The cut of **Lemma 21**, p.13. For a directed graph `G₁` with vertex heights `h`, the undirected graph `G₂` has vertex set `V × Fin 2` and, for each edge `(u, v)` of
`G₁`, the two copies `(u⁰, v⁰)` and `(u¹, v¹)`. This is the set `S = {u⁰ : h(u) ≥ 0} ∪ {u¹ : h(u) ≥ 1}`.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 21, p.13. -/
def heightCut {V : Type*} (h : V → ℤ) : Set (V × Fin 2) :=
  {x | (x.2 = 0 ∧ 0 ≤ h x.1) ∨ (x.2 = 1 ∧ 1 ≤ h x.1)}

end SkewMatching


