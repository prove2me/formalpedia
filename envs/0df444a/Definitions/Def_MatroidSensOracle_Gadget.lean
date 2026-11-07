-- Prove2me | Definitions.Def_MatroidSensOracle_Gadget
-- name    : MatroidSensOracle_Gadget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:24.223532+00:00
-- url     : https://prove2.me/theorems/1ffb4515-1dd7-4113-8f17-9fb27b9c242a
-- title:
--   The §5.1 gadget (corrected: $k-\lambda$ bypass edges $s^*\to t^*$), the partition matroids $M_{\mathrm{out}}$, $M_{\mathrm{in}}$, and edge-disjoint paths
-- statement:
--   Let $H$ be a directed multigraph with a source $s^*$ and a sink $t^*$, and let $k\ge1$. The **gadget** adds $k$ self-loops at every vertex $v\notin\{s^*,t^*\}$ and $b$ parallel edges from $s^*$ to $t^*$; Lemma 5.1 uses $b=k-\lambda$, where $\lambda$ is the out-degree of $s^*$ and the in-degree of $t^*$.
--
--   On the edges of a digraph:
--   1. $S$ is independent in $M_{\mathrm{out}}$ if no edge of $S$ leaves $t^*$ and every vertex has at most one outgoing edge in $S$ — linear independence of the columns of $A_{\mathrm{out}}$, whose column for $e=(u,v)$ has a $1$ in row $u$ if $u\ne t^*$ and is zero otherwise.
--   2. $S$ is independent in $M_{\mathrm{in}}$ if no edge of $S$ enters $s^*$ and every vertex has at most one incoming edge in $S$.
--   3. A basis is a maximal independent set.
--
--   An $(s,t)$-**path** is a nonempty sequence of edges from $s$ to $t$, each starting at the head of the previous one, with no vertex repeated; $H$ contains $\lambda$ **edge-disjoint paths** if there are $\lambda$ such paths, pairwise without common edges.
--
--   **Formalization Note** The paper adds $k-\lambda$ self-loops at $s^*$ and at $t^*$. Those loops have zero columns in $A_{\mathrm{in}}$ and $A_{\mathrm{out}}$ respectively, and Lemma 5.1 then fails whenever $\lambda<k$; the gadget here uses $k-\lambda$ edges $s^*\to t^*$ instead. Where the paper's bulleted sentence and its matrices differ (an edge leaving $t^*$ or entering $s^*$), the matrices are followed; they give the printed rank $N-1$. Costs are irrelevant here and omitted.
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), §5.1, p.25 (PDF p.28); §2, p.12 (PDF p.15) for paths

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph
import Definitions.Def_MatroidSensOracle_LinearMatroid

set_option autoImplicit false

namespace MatroidSensOracle

/-!
# Edge-disjoint paths, the §5.1 gadget (corrected) and the partition matroids `M_out`, `M_in`

Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), §5.1, p.25 (PDF p.28):
"Let k be a positive integer, and H = (V_H, E_H) be a fixed directed multigraph on N vertices with a
designated source s∗ and a designated sink t∗ such that the out-degree of s∗ and the in-degree of t∗
are both equal to λ ⩽ k. We add to each vertex v ∈ V_H \ {s∗, t∗} a set of exactly k zero-cost
self-loops, and to vertices s∗ and t∗ we add k − λ zero-cost self-loops. […]
• M_out: A subset S ⊆ E_H is independent if every vertex v ∈ V_H \ {t∗} has at most one outgoing edge
  in S. This is represented by a matrix A_out ∈ {0, 1}^{(N−1)×M}, where rows are indexed by
  V_H \ {t∗}. The column for an edge e = (u, v) has a 1 at row u (if u ≠ t∗) and 0 elsewhere.
• M_in: […] rows are indexed by V_H \ {s∗}. The column for an edge e = (u, v) has a 1 at row v
  (if v ≠ s∗) and 0 elsewhere. Both matroids have rank N − 1."

Trail and path (§2, p.12): "A trail P from edge e0 to edge eℓ in G is a sequence of distinct edges
(e0, e1, …, eℓ) with head(ei) = tail(ei+1) for each 0 ⩽ i < ℓ (vertices may repeat). […] A trail is
a path if no vertex repeats."

**Formalization Note.**
* **Correction.** As printed, the `k − λ` self-loops at `s∗` and at `t∗` are loops of `M_in` and
  `M_out` (zero columns), and Lemma 5.1 fails whenever `λ < k` (e.g. `k = 1`, `λ = 0`, two vertices,
  no edges). The gadget here adds instead `k − λ` zero-cost **parallel edges from `s∗` to `t∗`** (the
  `bypass` edges), so that `s∗` has out-degree `k` and `t∗` in-degree `k`. Costs play no role in
  Lemma 5.1 and are omitted.
* **Partition matroids from the matrices.** `IndepOut`: no edge of `S` leaves `t∗` and every vertex
  has at most one outgoing edge in `S`; this is exactly linear independence of the columns of
  `A_out` (an edge leaving `t∗` has the zero column, a loop of the matroid). `IndepIn` symmetrically.
  The bulleted sentence and the matrix agree when no edge leaves `t∗` or enters `s∗`; the matrix
  (which gives the printed rank `N − 1`) is followed.
* A basis is a maximal independent set (Definition 2.8).
-/

open CombOpt.MinCostFlow

variable {V E : Type}

/-- The edges of the corrected gadget: the edges of `H`, `k` self-loops `(v, j)` at each
`v ∉ {s∗, t∗}`, and `b` bypass edges `s∗ → t∗`. -/
abbrev GadgetEdge (V E : Type) (s t : V) (k b : ℕ) :=
  E ⊕ ({v : V // v ≠ s ∧ v ≠ t} × Fin k) ⊕ Fin b

/-- The corrected gadget digraph of `H` with `k` loops at each inner vertex and `b` bypass edges. -/
def gadget (H : Digraph V E) (s t : V) (k b : ℕ) : Digraph V (GadgetEdge V E s t k b) where
  tail
    | .inl e => H.tail e
    | .inr (.inl p) => p.1.1
    | .inr (.inr _) => s
  head
    | .inl e => H.head e
    | .inr (.inl p) => p.1.1
    | .inr (.inr _) => t

/-- Independence in `M_out`: no edge of `S` leaves `t∗`, and every vertex has at most one outgoing
edge in `S`. -/
def IndepOut {E' : Type} [DecidableEq V] (D : Digraph V E') (t : V) (S : Finset E') : Prop :=
  (∀ e ∈ S, D.tail e ≠ t) ∧ ∀ v, (S.filter fun e => D.tail e = v).card ≤ 1

/-- Independence in `M_in`: no edge of `S` enters `s∗`, and every vertex has at most one incoming
edge in `S`. -/
def IndepIn {E' : Type} [DecidableEq V] (D : Digraph V E') (s : V) (S : Finset E') : Prop :=
  (∀ e ∈ S, D.head e ≠ s) ∧ ∀ v, (S.filter fun e => D.head e = v).card ≤ 1

/-- `p` is an `(s, t)`-path: a nonempty sequence of edges from `s` to `t`, each starting where the
previous one ends, with no vertex repeated. -/
def IsPath (H : Digraph V E) (s t : V) (p : List E) : Prop :=
  p ≠ [] ∧ (p.head?.map H.tail = some s) ∧ (p.getLast?.map H.head = some t) ∧
    p.IsChain (fun e e' => H.head e = H.tail e') ∧ (s :: p.map H.head).Nodup

/-- `H` contains `l` pairwise edge-disjoint `(s, t)`-paths. -/
def HasEdgeDisjointPaths (H : Digraph V E) (s t : V) (l : ℕ) : Prop :=
  ∃ P : Fin l → List E, (∀ i, IsPath H s t (P i)) ∧ ∀ i j, i ≠ j → ∀ e ∈ P i, e ∉ P j

end MatroidSensOracle


