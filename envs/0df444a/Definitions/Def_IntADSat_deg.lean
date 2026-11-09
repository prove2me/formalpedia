-- Prove2me | Definitions.Def_IntADSat_deg
-- name    : IntADSat_deg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:14.312225+00:00
-- url     : https://prove2.me/theorems/22d1bf26-c447-4969-8638-61f2211cc920
-- title:
--   Vertex degree $\deg_G(v)$
-- statement:
--   For a simple graph $G$ on $[n]$ and a vertex $v$, $\deg_G(v)$ is the number of neighbours of $v$. It is the $v$-th diagonal entry of $D_G=\operatorname{diag}(A_Ge)$.
--
--   **Formalization Note** Defined as the cardinality (`Set.ncard`) of the neighbour set, exactly the diagonal entry of the published `degreeMatrix`; it equals Mathlib's `SimpleGraph.degree` (proved in the mission's sanity file).
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Appendix A, p.11 (PDF 12), and Appendix B

import Mathlib

set_option autoImplicit false

namespace IntADSat

/-- The degree `deg_G(v)` of a vertex: the number of its neighbours
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Appendix A, p.11 (PDF 12), and throughout Appendix B).

**Formalization Note** Written as `Set.ncard` of the neighbour set, which is exactly the diagonal
entry of the published `UniformADProbes.Trace.degreeMatrix`; it equals `G.degree v`. -/
noncomputable def deg {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  Set.ncard (G.neighborSet v)

end IntADSat


