-- Prove2me | Definitions.Def_ImplicitParityWL_Supplement_Codes
-- name    : ImplicitParityWL_Supplement_Codes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:24:52.258975+00:00
-- url     : https://prove2.me/theorems/dbe1889e-c4b3-425d-9b96-67e9a302de12
-- title:
--   Edge-list codes of graphs and codes of colored graphs
-- statement:
--   Words are finite bit strings, and a natural number $n$ is written in the self-delimiting code $\langle n\rangle$ of the published `VariableWL` definition (the length of the binary expansion in unary, a separator, then the binary digits).
--
--   1. The **edge-list code** of an uncolored graph $G$ on the vertices $0,\dots,n-1$ with $m$ edges is
--   $$\langle n\rangle\,\langle m\rangle\,\langle i_1\rangle\langle j_1\rangle\cdots\langle i_m\rangle\langle j_m\rangle,$$
--   where $\{i_1,j_1\},\dots,\{i_m,j_m\}$ are the edges with $i_t<j_t$, listed in lexicographic order of $(i_t,j_t)$.
--   2. The **code of a colored graph** $G$ on the vertices $0,\dots,N-1$ with colors in $\mathbb N$ is $\langle N\rangle$, then the colors $\langle\chi_G(0)\rangle\cdots\langle\chi_G(N-1)\rangle$, then the number of edges and the edge records as above.
--   3. $E(G)$ denotes the number of edges of a colored graph.
--
--   The edge-list code is the input format of $k$-WL Distinguishing for fixed $k$ (Theorem 1.1); its length is $O((n+m)\log n)$, so a running time measured in the number of vertices is not dominated by reading an adjacency matrix. The colored-graph code is the output format of the register-program compiler (Theorem 8.6), whose proof emits vertex and edge records (Lemma 7.2).
--
--   **Formalization Note** The paper fixes neither format; these are the natural ones for the stated time bounds.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §1.1, p.2 (input of k-WL Distinguishing); Lemma 7.2, p.38 (vertex and edge records)

import Mathlib
import Definitions.Def_VariableWL
import Definitions.Def_ImplicitParityWL_ColoredGraph

namespace ImplicitParityWL

namespace Supplement

open OAI.VariableWL

/-- The edge records of a graph on `Fin n` (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the
Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, Lemma 7.2,
p.38: "vertex and edge records"): every edge `{i, j}` with `i < j`, as `integerCode i ++ integerCode j`,
in lexicographic order of `(i, j)`. -/
noncomputable def edgeRecords {n : ℕ} (G : SimpleGraph (Fin n)) : List Word := by
  classical
  exact (List.finRange n).flatMap fun i => (List.finRange n).filterMap fun j =>
    if i < j ∧ G.Adj i j then some (integerCode i.val ++ integerCode j.val) else none

/-- The **edge-list code** of an uncolored graph (§1.1, p.2, the input of `k`-WL Distinguishing for
fixed `k`): its order, its number of edges, then its edge records.

**Formalization Note** The paper fixes no input format. An edge list has length `O((n + m) log n)`,
so a time bound in `n` is not absorbed by reading an adjacency matrix. -/
noncomputable def edgeCode (G : Graph) : Word :=
  integerCode G.order ++ integerCode (edgeRecords G.graph).length ++ (edgeRecords G.graph).flatten

/-- The number of edges of a colored graph. -/
noncomputable def edgeCount {K V : Type*} (G : ColoredGraph K V) : ℕ := G.graph.edgeSet.ncard

/-- The **code of a colored graph** on `Fin N` with natural-number colors (Lemma 7.2, p.38): `N`, the
color of each vertex in order, the number of edges, then the edge records. -/
noncomputable def coloredCode {N : ℕ} (G : ColoredGraph ℕ (Fin N)) : Word :=
  integerCode N ++ (List.ofFn fun i : Fin N => integerCode (G.χ i)).flatten ++
    integerCode (edgeRecords G.graph).length ++ (edgeRecords G.graph).flatten

end Supplement

end ImplicitParityWL


