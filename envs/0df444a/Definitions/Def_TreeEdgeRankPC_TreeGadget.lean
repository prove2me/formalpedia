-- Prove2me | Definitions.Def_TreeEdgeRankPC_TreeGadget
-- name    : TreeEdgeRankPC_TreeGadget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:32.229004+00:00
-- url     : https://prove2.me/theorems/57ea7da2-1fac-410b-bcec-b7fbf0541e69
-- title:
--   The branch gadget $B_q$ and the tree $T(q_1,\dots,q_d)$
-- statement:
--   For a positive integer $q$, write the binary expansion of $q-1$ as $q=1+\sum_{j=1}^t 2^{a_j}$. The **branch gadget** $B_q$ starts from an edge $rr_q$, rooted at $r$, and attaches a star graph with $a_j+1$ edges at $r_q$ by one of its leaves, for each $j$. The tree $T(q_1,\dots,q_d)$ is obtained by identifying the roots of $B_{q_1},\dots,B_{q_d}$.
--
--   So the star's center is a child of $r_q$ with $a_j$ further leaves, and every vertex lies within distance three of the root. These are the gadgets of the reduction from GreedyAllocation to Tree-Edge-Ranking.
--
--   **Formalization Note** The numbering is that of the proof of Lemma 4.3, p.16: the common root is vertex $0$, then branches in input order, each with $r_{q}$ first, stars in increasing size, and each center before its leaves. A parent list `treeParents 1 q` gives the parent of every nonroot vertex. For example $T(12,3,1)$ of Figure 2 has parent list $[0,1,1,3,1,5,5,5,0,9,10,0]$.
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), §4.1, pp.15–16

import Mathlib

namespace TreeEdgeRankPC

/-- The graph on `0, …, ps.length` with a parent list: for `i < ps.length`, vertex `i + 1` is joined to the
vertex `ps[i]`. -/
def ofParents (ps : List ℕ) : SimpleGraph (Fin (ps.length + 1)) :=
  SimpleGraph.fromRel fun u v => ∃ i, (u : ℕ) = i + 1 ∧ ps[i]? = some (v : ℕ)

/-- The exponents `a₁ < … < a_t` of the binary expansion `m = Σ_j 2^{a_j}`, §4.1, p.15 (arXiv:2610.12438,
held version of 2026-11-02, sha256 9e04ca7b…), with `m = q − 1`. -/
def expansion (m : ℕ) : List ℕ := (List.range (Nat.size m)).filter m.testBit

/-- The parent list of the stars of a branch gadget, attached at the vertex `hub`, with `s` the next free
vertex number. "attach a star graph with (a_j + 1) edges at r_q by one of its leaves": the star's center is
a child of `hub` and has `a_j` further leaves. Each center is numbered before its leaves, and stars in
increasing size (p.16). -/
def starParents (hub : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | s, a :: as => hub :: List.replicate a s ++ starParents hub (s + a + 1) as

/-- The parent list of the gadget `B_q`, §4.1, p.15, with root `0` and `s` the next free vertex number:
"Start from an edge r r_q, rooted at r", with `r_q` numbered `s`, then the stars. -/
def gadgetParents (s q : ℕ) : List ℕ := 0 :: starParents s (s + 1) (expansion (q - 1))

/-- The parent list of `T(q₁, …, q_d)`, "Number the common root first, then branches in input order" (p.16). -/
def treeParents : ℕ → List ℕ → List ℕ
  | _, [] => []
  | s, q :: qs => gadgetParents s q ++ treeParents (s + (gadgetParents s q).length) qs

/-- **`T(q₁, …, q_d)`**, §4.1, p.16: "Now we obtain T(q1, ..., qd) by identifying the roots of Bq1, ..., Bqd."
The common root is vertex `0`.

**Formalization Note.** The vertices are numbered as in the proof of Lemma 4.3, p.16. -/
def treeOfRequirements (q : List ℕ) : SimpleGraph (Fin ((treeParents 1 q).length + 1)) :=
  ofParents (treeParents 1 q)

/-- The **branch gadget `B_q`**, §4.1, p.15: "Write the binary expansion of q − 1 as q = 1 + Σ_{j=1}^t 2^{a_j}.
Start from an edge r r_q, rooted at r, and attach a star graph with (a_j + 1) edges at r_q by one of its
leaves for each j." It is rooted at vertex `0`, and for `q = 1` it is the single edge `r r_q`. -/
def gadget (q : ℕ) : SimpleGraph (Fin ((treeParents 1 [q]).length + 1)) := treeOfRequirements [q]

end TreeEdgeRankPC


