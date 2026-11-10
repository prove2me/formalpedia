-- Prove2me | Definitions.Def_BipDijoin_IsMatching
-- name    : BipDijoin_IsMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:18.917567+00:00
-- url     : https://prove2.me/theorems/316a36f4-b41e-475a-b945-36570efebca0
-- title:
--   Matchings, maximum and perfect matchings, and the deficiency $\alpha(G)$
-- statement:
--   A **matching** of a bipartite multigraph $G$ is a set $M$ of edges no two of which share an end. A vertex is **covered** by $M$ if it is an end of an edge of $M$. A **maximum matching** has the largest cardinality, and a **perfect matching** covers every vertex.
--
--   The **deficiency** $\alpha(G)$ is the minimum, over all matchings $M$ of $G$, of the number of vertices that $M$ leaves uncovered (Theorem 3.5: "the minimum number of unmatched terminals in G for any matching").
--
--   These notions underlie the alternating digraph, strong ends and end decompositions.
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), §2.2, p.3 (PDF p.5); Theorem 3.5, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph

set_option autoImplicit false

namespace BipDijoin

/-!
# Matchings of a bipartite multigraph

Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6), §2.2, p.3 (PDF p.5),
and Theorem 3.5, p.7 (PDF p.9): "Let α denote the minimum number of unmatched terminals in G for
any matching".

**Formalization Note.**
* A matching is a set of edge identities, no two of which share an end.
* `deficiency G` is `α(G)`: the minimum, over all matchings, of the number of vertices of `V`
  that the matching leaves uncovered.
-/

namespace BipGraph

variable (G : BipGraph)

/-- A **matching**: edges of `G`, no two distinct ones sharing an end. -/
def IsMatching (M : Finset ℕ) : Prop :=
  M ⊆ G.E ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f →
    G.tl e ≠ G.tl f ∧ G.hd e ≠ G.hd f ∧ G.tl e ≠ G.hd f ∧ G.hd e ≠ G.tl f

/-- `v` is covered (matched) by the edge set `M`. -/
def covered (M : Finset ℕ) (v : ℕ) : Prop := ∃ e ∈ M, G.tl e = v ∨ G.hd e = v

/-- A **maximum matching**: a matching of largest cardinality. -/
def IsMaxMatching (M : Finset ℕ) : Prop :=
  G.IsMatching M ∧ ∀ M', G.IsMatching M' → M'.card ≤ M.card

/-- A **perfect matching**: a matching covering every vertex. -/
def IsPerfectMatching (M : Finset ℕ) : Prop := G.IsMatching M ∧ ∀ v ∈ G.V, G.covered M v

/-- `G` is perfectly matchable. -/
def HasPerfectMatching : Prop := ∃ M, G.IsPerfectMatching M

open Classical in
/-- `α(G)`: the minimum number of vertices left unmatched by a matching of `G`
(Theorem 3.5, p.7). -/
noncomputable def deficiency : ℕ :=
  sInf {k | ∃ M, G.IsMatching M ∧ k = (G.V.filter (fun v => ¬ G.covered M v)).card}

end BipGraph

end BipDijoin


