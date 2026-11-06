-- Prove2me | Definitions.Def_TreeMultiflow_RatInstance_src
-- name    : TreeMultiflow_RatInstance_src
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:03.99525+00:00
-- url     : https://prove2.me/theorems/317f431f-6961-46e8-a8d6-ff704f892b6a
-- title:
--   First endpoint of a request of a rational instance
-- statement:
--   The first endpoint $s$ of the request $(s,t,w,x)$ in position $f$ of the request list.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 1, p.2 (the endpoints of a request)

import Mathlib
import Definitions.Def_TreeMultiflow_RatInstance_vertex

namespace TreeMultiflow

/-- **The first endpoint of each request of a rational instance.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 1,
p.2 ("Path(f), the unique path between its endpoints on the tree").

The requests of `I` are indexed by `Fin I.reqs.length`; `I.src f` is the first endpoint
of the `f`-th entry of `I.reqs`. -/
def RatInstance.src (I : RatInstance) (f : Fin I.reqs.length) : Fin (I.n + 1) :=
  I.vertex (I.reqs.get f).1

end TreeMultiflow


