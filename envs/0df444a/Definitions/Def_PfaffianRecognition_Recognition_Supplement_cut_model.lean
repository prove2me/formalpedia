-- Prove2me | Definitions.Def_PfaffianRecognition_Recognition_Supplement_cut_model
-- name    : PfaffianRecognition_Recognition_Supplement_cut_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:59:10.018856+00:00
-- url     : https://prove2.me/theorems/3b324806-34fe-4a4e-8710-1c86cc500029
-- title:
--   Cut reversal $D^X$, strong connectivity, matching covered and conformal subgraphs, oddly oriented cycles, odd ears
-- statement:
--   Let $G$ be a finite simple graph on the ordered vertex set $\{0,\ldots,N-1\}$ and let $D$ be an orientation of $G$ (one direction on each edge, none on a non-edge), as in the published graph model.
--
--   1. **Cut reversal.** For a vertex set $X\subseteq V(G)$, the cut $\partial(X)$ consists of the edges with exactly one endpoint in $X$. The orientation $D^X$ reverses every edge of $\partial(X)$ and keeps every other edge:
--   $$
--   D^X(i,j)\iff\bigl(|\{i,j\}\cap X|=1\text{ and }D(j,i)\bigr)\ \text{or}\ \bigl(|\{i,j\}\cap X|\ne1\text{ and }D(i,j)\bigr).
--   $$
--   $D^X$ is again an orientation of $G$; $X$ ranges over all subsets, $\emptyset$ and $V(G)$ included.
--   2. **Strong connectivity.** An orientation is strongly connected when every vertex is reachable from every vertex by a directed path (the published digraph predicate applied to the arcs of the orientation).
--   3. **Matching covered.** A subgraph $H$ of $G$ is matching covered when it is connected, has at least one edge, and every edge of $H$ lies in a perfect matching of $H$ (a set of edges of $H$ covering every vertex of $H$ exactly once). $G$ itself is matching covered when the same holds with the perfect matchings of $G$.
--   4. **Conformal.** A vertex set $S$, or a subgraph with vertex set $S$, is conformal when $G-S$ has a perfect matching.
--   5. **Oddly oriented.** A closed walk $v_0v_1\cdots v_{\ell-1}v_0$ is oddly oriented in $D$ when an odd number of its edges are directed along the traversal, i.e. $D(v_i,v_{i+1})$ for an odd number of $i$; for an even cycle this parity does not depend on the direction of traversal.
--   6. **Odd ears and ear steps.** An odd ear of a subgraph $H$ is a path of odd length whose endpoints lie in $V(H)$, whose internal vertices lie outside $V(H)$, and none of whose edges is an edge of $H$. $H'$ is obtained from $H$ by an ear step when $H'=H\cup P$ for one odd ear $P$ of $H$, or $H'=H\cup P\cup Q$ for two odd ears $P,Q$ of $H$ with no common vertex.
--
--   These are the objects of §1 (p. 4) and §4 (p. 12) used in Theorem 1.2 and Lemmas 4.1–4.3.
--
--   **Formalization Note** Cycles, paths and ears are Mathlib walks (`IsCycle`, `IsPath`); subgraphs are `G.Subgraph` with `⊤` for $G$; adding an ear is the supremum with the ear's subgraph. Matching covered is not defined in the paper; the standard definition of Lovász–Plummer and Lucchesi–Murty is used.
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), §1, pp. 3–4 (conformal subgraph, oddly oriented, strongly connected, ∂(X), D^X); §4, p. 12 (odd ear, ear decomposition); matching covered as in [LP86], [LM24]; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Mathlib
import Definitions.Def_PfaffianRecognition_Recognition_graph_model
import Definitions.Def_FASTournament_IsStrong

noncomputable section

namespace PfaffianRecognition.Recognition.Supplement

open PfaffianRecognition.Recognition

/-- §1, p. 4: `D^X`, the orientation obtained from `D` by reversing every edge of the cut
`∂(X)`, i.e. every edge with exactly one endpoint in `X`. Edges inside `X` or inside its
complement keep their direction. `X` is an arbitrary vertex set, `∅` and all of `V(G)` included. -/
def cutReversal {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G) (X : Set (Fin N)) :
    Orientation G :=
  ⟨fun i j => (¬ (i ∈ X ↔ j ∈ X) ∧ D.val j i) ∨ ((i ∈ X ↔ j ∈ X) ∧ D.val i j), by
    obtain ⟨hD₁, hD₂⟩ := D.property
    refine ⟨fun u v h => ?_, fun u v h => ?_⟩
    · rcases h with ⟨_, h⟩ | ⟨_, h⟩
      · exact (hD₁ v u h).symm
      · exact hD₁ u v h
    · obtain ⟨h₁, h₂⟩ := hD₂ u v h
      have hx : (v ∈ X ↔ u ∈ X) ↔ (u ∈ X ↔ v ∈ X) := Iff.comm
      show (((¬ (u ∈ X ↔ v ∈ X) ∧ D.val v u) ∨ ((u ∈ X ↔ v ∈ X) ∧ D.val u v)) ∨
          ((¬ (v ∈ X ↔ u ∈ X) ∧ D.val u v) ∨ ((v ∈ X ↔ u ∈ X) ∧ D.val v u))) ∧
        ¬ (((¬ (u ∈ X ↔ v ∈ X) ∧ D.val v u) ∨ ((u ∈ X ↔ v ∈ X) ∧ D.val u v)) ∧
          ((¬ (v ∈ X ↔ u ∈ X) ∧ D.val u v) ∨ ((v ∈ X ↔ u ∈ X) ∧ D.val v u)))
      rw [hx]
      by_cases hc : (u ∈ X ↔ v ∈ X) <;> simp only [hc, not_true_eq_false, not_false_eq_true,
        true_and, false_and, false_or, or_false] <;> tauto⟩

/-- §1, p. 4: an orientation is strongly connected when every vertex is reachable from every
vertex by a directed path, i.e. the published digraph strong-connectivity predicate applied to the
arc relation of the orientation on all of `Fin N`. -/
def IsStronglyConnected {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G) : Prop :=
  FASTournament.IsStrong (⟨D.val⟩ : Digraph (Fin N))

/-- A perfect matching of a subgraph `H` of `G`: a set of edges of `H` covering every vertex of
`H` exactly once. For `H = ⊤` this is the published `IsPerfectMatchingEdges G`. -/
def IsSubgraphPerfectMatching {N : ℕ} {G : SimpleGraph (Fin N)} (H : G.Subgraph)
    (M : Finset G.edgeSet) : Prop :=
  (∀ e ∈ M, (e : Sym2 (Fin N)) ∈ H.edgeSet) ∧
    ∀ v ∈ H.verts, ∃! e, e ∈ M ∧ v ∈ (e : Sym2 (Fin N))

/-- Matching covered subgraph (standard notion of Lovász–Plummer, used on pp. 3–4, 12–14):
`H` is connected, has at least one edge, and every edge of `H` lies in some perfect matching
of `H`. -/
def IsMatchingCoveredSubgraph {N : ℕ} {G : SimpleGraph (Fin N)} (H : G.Subgraph) : Prop :=
  H.Connected ∧ H.edgeSet.Nonempty ∧
    ∀ e ∈ H.edgeSet, ∃ M : Finset G.edgeSet, IsSubgraphPerfectMatching H M ∧
      ∃ f ∈ M, (f : Sym2 (Fin N)) = e

/-- A matching covered graph: connected, with at least one edge, every edge in a perfect
matching (`IsPerfectMatchingEdges`). -/
def IsMatchingCovered {N : ℕ} (G : SimpleGraph (Fin N)) : Prop :=
  G.Connected ∧ G.edgeSet.Nonempty ∧
    ∀ e : G.edgeSet, ∃ M : Finset G.edgeSet,
      MulmuleyVV.Matching.IsPerfectMatchingEdges G M ∧ e ∈ M

/-- p. 3: a vertex set `S` is conformal when `G − S` has a perfect matching: some set of edges of
`G`, none meeting `S`, covers every vertex outside `S` exactly once. A subgraph is conformal when
its vertex set is. -/
def IsConformalSet {N : ℕ} (G : SimpleGraph (Fin N)) (S : Set (Fin N)) : Prop :=
  ∃ M : Finset G.edgeSet, (∀ e ∈ M, ∀ v ∈ (e : Sym2 (Fin N)), v ∉ S) ∧
    ∀ v, v ∉ S → ∃! e, e ∈ M ∧ v ∈ (e : Sym2 (Fin N))

/-- Number of edges of a closed walk `v₀ v₁ ⋯ v₀` directed along its direction of traversal
(darts `vᵢ → vᵢ₊₁` with `D vᵢ vᵢ₊₁`). -/
def forwardCount {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G) {u v : Fin N}
    (p : G.Walk u v) : ℕ := by
  classical
  exact (p.darts.filter fun d => D.val d.fst d.snd).length

/-- p. 3: an (even) cycle is oddly oriented in `D` when an odd number of its edges are
directed along its direction of traversal. -/
def IsOddlyOriented {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G) {u : Fin N}
    (p : G.Walk u u) : Prop :=
  Odd (forwardCount D p)

/-- p. 12: an odd ear of a subgraph `H`: a path of odd length with both endpoints in `V(H)`, all
other (internal) vertices outside `V(H)`, and no edge in `H`. -/
def IsOddEar {N : ℕ} {G : SimpleGraph (Fin N)} (H : G.Subgraph) {a b : Fin N}
    (p : G.Walk a b) : Prop :=
  p.IsPath ∧ Odd p.length ∧ a ∈ H.verts ∧ b ∈ H.verts ∧
    (∀ v ∈ p.support, v ≠ a → v ≠ b → v ∉ H.verts) ∧
    ∀ e ∈ p.edges, e ∉ H.edgeSet

/-- p. 12: `H'` is obtained from `H` by adding one odd ear, or two vertex-disjoint odd ears
(no common vertex, endpoints included); the added ears contribute their vertices and edges. -/
def IsEarStep {N : ℕ} {G : SimpleGraph (Fin N)} (H H' : G.Subgraph) : Prop :=
  (∃ (a b : Fin N) (p : G.Walk a b), IsOddEar H p ∧ H' = H ⊔ p.toSubgraph) ∨
  (∃ (a b c d : Fin N) (p : G.Walk a b) (q : G.Walk c d),
      IsOddEar H p ∧ IsOddEar H q ∧ (∀ v ∈ p.support, v ∉ q.support) ∧
      H' = H ⊔ p.toSubgraph ⊔ q.toSubgraph)

end PfaffianRecognition.Recognition.Supplement


