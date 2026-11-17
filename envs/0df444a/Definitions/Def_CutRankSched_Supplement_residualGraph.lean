-- Prove2me | Definitions.Def_CutRankSched_Supplement_residualGraph
-- name    : CutRankSched_Supplement_residualGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:48:24.116191+00:00
-- url     : https://prove2.me/theorems/3e34a28d-2a6f-460f-af04-a8587d4521d8
-- title:
--   The residual conflict graph $X^\circ$ as a simple graph
-- statement:
--   The **residual exposure-conflict graph** $X^\circ$ is the simple graph on the events whose edges are the residual pairs $E(X^\circ)=E_X\setminus E_{\mathrm{anti}}$: distinct events with overlapping exposure regions whose Paulis commute. Its chromatic number $\chi(X^\circ)$ enters Theorem 6.1.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.2, p.4, and Section 6.1, p.11

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Residual

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The residual exposure-conflict graph `X°` as a simple graph on the events (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.2, p.4,
and §6.1, p.11): `{i, j}` is an edge iff `{i, j} ∈ E(X°)`.

**Formalization Note** `SimpleGraph.fromRel` symmetrizes and drops loops; `Residual` is already
symmetric and irreflexive, so the adjacency is exactly `Residual I i j`. -/
def residualGraph (I : Instance) : SimpleGraph (Fin I.n) :=
  SimpleGraph.fromRel (Residual I)

end Supplement

end CutRankSched


