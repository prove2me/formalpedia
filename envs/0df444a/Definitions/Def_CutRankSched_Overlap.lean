-- Prove2me | Definitions.Def_CutRankSched_Overlap
-- name    : CutRankSched_Overlap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:31:22.06448+00:00
-- url     : https://prove2.me/theorems/8d2c3bca-b66a-4b69-9820-3e336cdd8a80
-- title:
--   Exposure-overlap edges $E_X$
-- statement:
--   The **exposure-overlap graph** on the events has edge set
--   $$
--   E_X = \{\, \{i, j\} : V(T_i) \cap V(T_j) \ne \emptyset \,\},
--   $$
--   the pairs of distinct events whose prescribed exposure regions share a hardware vertex.
--
--   **Formalization Note** As an edge set of a simple graph, $E_X$ consists of pairs of **distinct** events; the Lean predicate requires $i \ne j$ and is symmetric.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.2, p.4

import Mathlib
import Definitions.Def_CutRankSched_Instance

set_option autoImplicit false

namespace CutRankSched

/-- The exposure-overlap edges `E_X = {{i, j} : V(T_i) ∩ V(T_j) ≠ ∅}` (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.2, p.4).

**Formalization Note** `E_X` is an edge set of an undirected simple graph on the events, so
`Overlap I i j` requires `i ≠ j`; it is symmetric in `i, j`. -/
def Overlap (I : Instance) (i j : Fin I.n) : Prop :=
  i ≠ j ∧ ((I.T i).verts ∩ (I.T j).verts).Nonempty

end CutRankSched


