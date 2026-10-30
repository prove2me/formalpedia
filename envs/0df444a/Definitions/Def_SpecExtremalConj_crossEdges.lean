-- Prove2me | Definitions.Def_SpecExtremalConj_crossEdges
-- name    : SpecExtremalConj_crossEdges
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:08:02.610514+00:00
-- url     : https://prove2.me/theorems/d2352e2a-4b51-4f71-ba28-75d4d5a5bc53
-- title:
--   Number of crossing edges $\sum_{i<j} e(V_i,V_j)$
-- statement:
--   For a graph $G$ and a partition $V(G)=V_1\cup\dots\cup V_r$, write $e(V_i,V_j)$ for the number of edges of $G$ between $V_i$ and $V_j$. The **number of crossing edges** of the partition is
--
--   $$\sum_{1\le i<j\le r} e(V_i,V_j),$$
--
--   the number of edges of $G$ whose two ends lie in different parts.
--
--   Lemma 3.3 works with a partition maximizing this quantity.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, §2, p. 2 (e(V_1, V_2)) and Lemma 3.3, p. 4

import Mathlib
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **Number of crossing edges Σ_{1≤i<j≤r} e(V_i, V_j).** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, §2, p. 2 ("e(V_1, V_2) denotes the
number of edges of G between V_1 and V_2") and §3, p. 4.

`crossEdges G P` is the number of edges of `G` whose two ends lie in different parts of the
partition `P : V → Fin r`; this is Σ_{i<j} e(V_i, V_j).

**Formalization Note.** Decidability of the filter is classical. -/
noncomputable def crossEdges {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : V → Fin r) : ℕ := by
  classical
  exact #{e ∈ G.edgeFinset | ∃ u ∈ e, ∃ v ∈ e, P u ≠ P v}

end SpecExtremalConj


