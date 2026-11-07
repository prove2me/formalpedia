-- Prove2me | Definitions.Def_DynEdgeOrient_DynamicGraph
-- name    : DynEdgeOrient_DynamicGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:27.290251+00:00
-- url     : https://prove2.me/theorems/99abb4b5-17e7-48c7-98a9-f92c45c95e4c
-- title:
--   Dynamic graphs under an arboricity $\alpha$-preserving sequence of updates
-- statement:
--   A **dynamic graph** is a sequence of states $G_0,G_1,\dots,G_m$ of a graph on a fixed vertex set, where $m=|U|$ is the number of updates and the update $u_i$ takes $G_{i-1}$ to $G_i$ by inserting or deleting exactly one edge:
--
--   $$
--   |G_{i-1}\,\triangle\,G_i|=1\qquad(1\le i\le m).
--   $$
--
--   The sequence is **arboricity $\alpha$-preserving** when every state $G_0,\dots,G_m$ has arboricity at most $\alpha$.
--
--   This is the paper's dynamic setting: an adversary adds or removes one edge per time step under the guarantee that the arboricity is always at most $\alpha$.
--
--   **Formalization Note** The states are a function $\mathbb N\to\mathrm{Finset}\,E$; only $G_0,\dots,G_m$ matter. Starting from the empty graph is a separate hypothesis, made only in Theorem 1.2; the results of §§4–5 allow an arbitrary $G_0$.
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), §1, p.1 (dynamic setting) and Remark 4.2, p.12

import Mathlib
import Definitions.Def_DynEdgeOrient_Multigraph

namespace DynEdgeOrient

/-!
# Dynamic graphs under an arboricity-preserving update sequence

S. Hiken, N. Wein, *Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n
Barrier*, STOC 2027 submission (manuscript sha256 626b4eee…), §1, p.1 ("at each time step an
adversary adds or removes an edge from the graph, under the guarantee that the arboricity is
always upper bounded by α") and Remark 4.2, p.12 ("update `u_i` transitions `G` from `G_{i−1}` to
`G_i`").

**Formalization Note.**
* A dynamic graph is a sequence of states `G : ℕ → Finset E`; `G i` is the state after the `i`-th
  update, and `m` is the number of updates `|U|`. Only `G 0, …, G m` matter.
* `IsDynamic G m`: every update `u_{i+1}` (`i < m`) changes exactly one edge, so
  `|G i ∆ G (i+1)| = 1`. It is an insertion if the edge is in `G (i+1)`, a deletion otherwise.
* `ArbPreserving ends G m α`: the arboricity is at most `α` at every time `0, …, m`.
* Whether `G 0 = ∅` is a separate hypothesis: Theorem 1.2 assumes it, Lemma 4.9 and the results of
  §§4–5 do not ("G0 is not necessarily the empty graph").
-/

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- The sequence `G 0, …, G m` changes by exactly one edge insertion or deletion per step. -/
def IsDynamic (G : ℕ → Finset E) (m : ℕ) : Prop :=
  ∀ i < m, (symmDiff (G i) (G (i + 1))).card = 1

/-- Every state `G 0, …, G m` has arboricity at most `α` (an arboricity `α`-preserving
sequence of updates). -/
def ArbPreserving (ends : E → V × V) (G : ℕ → Finset E) (m α : ℕ) : Prop :=
  ∀ i ≤ m, ArboricityLE ends (G i) α

end DynEdgeOrient


