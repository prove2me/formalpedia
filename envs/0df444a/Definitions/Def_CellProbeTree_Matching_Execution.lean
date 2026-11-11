-- Prove2me | Definitions.Def_CellProbeTree_Matching_Execution
-- name    : CellProbeTree_Matching_Execution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:34:52.052357+00:00
-- url     : https://prove2.me/theorems/33c7972c-73c4-40a4-a25b-438e0051b580
-- title:
--   Valid states and actual execution paths of an exact adaptive query algorithm
-- statement:
--   A **state** is a header $P$ (from some set of headers) and an ordinary memory $M \in (\{0,1\}^w)^s$. The query algorithm is deterministic once the header is given: for every header $P$ and **physical query** $q$ it is a fully adaptive probe tree over the $s$ cells, with answers in a set of answers. Given a **specification** assigning to each state and query its correct answer, a state $(P, M)$ is **valid** when the algorithm, run on $M$ with header $P$, returns the correct answer to every physical query. The **actual execution path** of $q$ on $(P, M)$ is the sequence of cell addresses read when the tree for $(P, q)$ runs on $M$.
--
--   **Formalization Note.** The algorithm is a function `alg : Hdr → Qry → DynOracleConn.ProbeTree (Fin s) (BitVec w) Ans`; the specification is any `spec : Hdr → (Fin s → BitVec w) → Qry → Ans`. `actualPath` lists the addresses of `ProbeTree.transcript`; its set of entries is the paper's $\mathrm{Probe}_X(q)$ (distinct addresses after memoizing repeated reads).
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 10, §3.1 (states, physical queries, Probe_X(q)) and p. 12, §3.2

import Mathlib
import Definitions.Def_DynOracleConn_ProbeTree

/-!
# Valid states and actual execution paths

Liang, Liu, *Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality*,
STOC 2027 submission, §3.1, p. 10 (states, physical queries, `Probe_X(q)`) and §3.2, p. 12.

A state is a header `P` and an ordinary memory `M : Fin s → BitVec w`. The query algorithm is
deterministic once the header is given: for each header and physical query it is a fully adaptive
probe tree over the cells. A state is valid when the algorithm answers every physical query
according to the common specification `spec`.
-/

namespace CellProbeTree.Matching

open DynOracleConn

variable {s w : ℕ} {Hdr Qry Ans : Type}

/-- The cell addresses read along the actual execution of the algorithm for header `P` and
physical query `q` on memory `M`, in order. -/
def actualPath (alg : Hdr → Qry → ProbeTree (Fin s) (BitVec w) Ans) (P : Hdr) (q : Qry)
    (M : Fin s → BitVec w) : List (Fin s) :=
  (ProbeTree.transcript (alg P q) M).map Prod.fst

/-- The state `(P, M)` is valid for the algorithm `alg` and the specification `spec` (the correct
answer of each physical query in each state): `alg` answers every physical query correctly. -/
def IsValidState (alg : Hdr → Qry → ProbeTree (Fin s) (BitVec w) Ans)
    (spec : Hdr → (Fin s → BitVec w) → Qry → Ans) (P : Hdr) (M : Fin s → BitVec w) : Prop :=
  ∀ q : Qry, ProbeTree.run (alg P q) M = spec P M q

end CellProbeTree.Matching


