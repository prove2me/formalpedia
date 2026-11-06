-- Prove2me | Definitions.Def_TreeMultiflow_pathEnd
-- name    : TreeMultiflow_pathEnd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:13.502198+00:00
-- url     : https://prove2.me/theorems/ade2f5f6-e763-4533-8d3c-2f2af4a0e013
-- title:
--   The two ends of a labeled path
-- statement:
--   A labeled path $p$ joins the vertices $a_p$ and $b_p$. Its two **ends** are indexed by $(p,\mathrm{false})$, located at $a_p$, and $(p,\mathrm{true})$, located at $b_p$.
--
--   Ends are the objects that are placed into bins: each path belongs to exactly one bin at each of its two endpoints.
--
--   **Formalization Note** The same device is used for the local paths of Lemma 5.1, whose ends lie in bins rather than at vertices.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 3, p.6 (Each path belongs to exactly one bin at each of its two endpoints)

import Mathlib

namespace TreeMultiflow

/-- **The two ends of a labeled path.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 3,
p.6: "Each path belongs to exactly one bin at each of its two endpoints."

A labeled path `p` joins `a p` and `b p`. Its two ends are `(p, false)` (at `a p`) and
`(p, true)` (at `b p`); `pathEnd a b ξ` is the vertex at the end `ξ`.

**Formalization Note.** Ends are indexed by `P × Bool` so that a bin can be specified at each end
separately. The same device serves the abstract star instance of Lemma 5.1 (p.8), with bins in
place of vertices. -/
def pathEnd {P V : Type*} (a b : P → V) (ξ : P × Bool) : V :=
  if ξ.2 then b ξ.1 else a ξ.1

end TreeMultiflow


