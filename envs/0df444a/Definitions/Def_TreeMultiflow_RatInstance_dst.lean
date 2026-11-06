-- Prove2me | Definitions.Def_TreeMultiflow_RatInstance_dst
-- name    : TreeMultiflow_RatInstance_dst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:54.0322+00:00
-- url     : https://prove2.me/theorems/31a3f251-c7b5-47ac-b632-00063cc8eb24
-- title:
--   Second endpoint of a request of a rational instance
-- statement:
--   The second endpoint $t$ of the request $(s,t,w,x)$ in position $f$ of the request list.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 1, p.2 (the endpoints of a request)

import Mathlib
import Definitions.Def_TreeMultiflow_RatInstance_vertex

namespace TreeMultiflow

/-- **The second endpoint of each request of a rational instance.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 1,
p.2 ("Path(f), the unique path between its endpoints on the tree").

The requests of `I` are indexed by `Fin I.reqs.length`; `I.dst f` is the second endpoint
of the `f`-th entry of `I.reqs`. -/
def RatInstance.dst (I : RatInstance) (f : Fin I.reqs.length) : Fin (I.n + 1) :=
  I.vertex (I.reqs.get f).2.1

end TreeMultiflow


