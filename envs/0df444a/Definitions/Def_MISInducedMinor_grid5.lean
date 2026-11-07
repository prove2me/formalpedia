-- Prove2me | Definitions.Def_MISInducedMinor_grid5
-- name    : MISInducedMinor_grid5
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:25.267434+00:00
-- url     : https://prove2.me/theorems/855baace-edcb-4134-8844-e29f3a4141f5
-- title:
--   The $5\times 5$ grid
-- statement:
--   The **$5\times 5$ grid** is the graph on $\{0,\dots,4\}^2$ in which $(a,b)$ and $(a',b')$ are adjacent iff they agree in one coordinate and differ by exactly one in the other; it is the Cartesian product $P_5\,\square\,P_5$ of two paths on five vertices.
--
--   It is the planar graph whose exclusion as an induced minor is the subject of Theorem 1.5.
--
--   **Formalization Note** The paper does not define the grid; this is the standard grid graph, Mathlib's `pathGraph 5 □ pathGraph 5`.
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), Theorem 1.5, p.3

import Mathlib

set_option autoImplicit false

namespace MISInducedMinor

/-- The **5 × 5 grid**: the Cartesian product of two paths on five vertices, on the vertex set
`Fin 5 × Fin 5`, where `(a, b)` and `(a', b')` are adjacent iff they agree in one coordinate and
differ by one in the other. arXiv:2609.11285 (sha256 e378b906…), Theorem 1.5, p.3.

**Formalization Note.** The paper does not define the grid; this is the standard grid graph,
`pathGraph 5 □ pathGraph 5` in Mathlib's notation. -/
def grid5 : SimpleGraph (Fin 5 × Fin 5) :=
  SimpleGraph.boxProd (SimpleGraph.pathGraph 5) (SimpleGraph.pathGraph 5)

end MISInducedMinor


