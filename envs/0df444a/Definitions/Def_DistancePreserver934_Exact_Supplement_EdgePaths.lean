-- Prove2me | Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
-- name    : DistancePreserver934_Exact_Supplement_EdgePaths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:19:43.404936+00:00
-- url     : https://prove2.me/theorems/283307f6-61f3-4210-8b1a-ac8f6ea33c2c
-- title:
--   Chosen edge-disjoint shortest paths
-- statement:
--   For an undirected graph $H$ and a finite unordered demand set $P$, a family assigns to every $q\in P$ an orientation $(s_q,t_q)$ and an actual $H$-walk of length $\operatorname{dist}_H(s_q,t_q)$. Distinct demands' walks have disjoint unordered edge sets:
--
--   $$E(\pi(q))\cap E(\pi(q'))=\varnothing\qquad(q\ne q').$$
--
--   This is the path data fixed in §4. It asserts neither shortest-path uniqueness nor any sparsity bound. The ambient graph and demand admissibility remain hypotheses of theorems using the family.
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; §4, printed pp. 9–10 (PDF pp. 10–11)

import Definitions.Def_DistancePreserver934_Exact_Essential

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

/-- An actual shortest walk realizing one unordered demand, with an orientation. -/
structure DemandPath {V : Type} (H : SimpleGraph V) (q : Sym2 V) where
  start : V
  finish : V
  endpoints : s(start, finish) = q
  walk : H.Walk start finish
  shortest : IsShortest walk

/-- The fixed mutually edge-disjoint shortest paths of §4. No uniqueness is assumed. -/
structure EdgeDisjointFamily {V : Type} (H : SimpleGraph V) (P : Finset (Sym2 V)) where
  path : (q : P) → DemandPath H q.val
  disjoint : ∀ q q' : P, q ≠ q' → ∀ e ∈ (path q).walk.edges, e ∉ (path q').walk.edges

end DistancePreserver934.Exact.Supplement


