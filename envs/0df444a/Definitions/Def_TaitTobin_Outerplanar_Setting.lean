-- Prove2me | Definitions.Def_TaitTobin_Outerplanar_Setting
-- name    : TaitTobin_Outerplanar_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:56:25.796559+00:00
-- url     : https://prove2.me/theorems/7fef385a-d1b8-4f8e-a981-38f0402deee7
-- title:
--   §1.2 and §2, pp. 3–6 — outerplanar graphs, graph join, the fan K₁ + Pₙ₋₁, spectral maximizers, e(X) and e(X, Y)
-- statement:
--   This file fixes the objects of Section 2 of Tait and Tobin. Graphs are finite simple graphs; an $n$-vertex graph has vertex set $\{0,\dots,n-1\}$. For a graph $G$, $\lambda_1(G)$ denotes the largest eigenvalue of its adjacency matrix (the published spectral radius `specRad`).
--
--   1. **Drawing image and outer face.** For a plane drawing $D$ of $G$ (vertices are distinct points of $\mathbb R^2$, edges are simple arcs between their ends that avoid the other vertices and meet only at common ends), the *image* $|D|$ is the union of the vertex points and the arcs. The *outer face* of $D$ is the set of points $p \notin |D|$ whose connected component in $\mathbb R^2 \setminus |D|$ is unbounded.
--   2. **Outerplanar graphs.** $G$ is *outerplanar* if it has a plane drawing $D$ in which every vertex point lies in the closure of the outer face, i.e. on the boundary of the unbounded face.
--   3. **Join.** For graphs $G$ on $\alpha$ and $H$ on $\beta$, the join $G + H$ is the graph on the disjoint union $\alpha \sqcup \beta$ that keeps the edges of $G$ and of $H$ and adds every edge between a vertex of $G$ and a vertex of $H$.
--   4. **The fan.** $K_1 + P_{n-1}$ is the join of a single vertex with the path on $n-1$ vertices (Figure 1 of the paper).
--   5. **Spectral maximizers.** For a property $P$ of graphs on $n$ vertices, $G$ is a spectral maximizer for $P$ if $G$ has $P$ and
--   $$\lambda_1(G') \le \lambda_1(G) \quad\text{for every graph } G' \text{ on the same } n \text{ vertices with } P.$$
--   6. **Edge counts.** For vertex sets $X, Y$, $e(X)$ is the number of edges with both ends in $X$, and $e(X,Y)$ is the number of edges with one end in $X$ and the other in $Y$, each edge counted once.
--
--   These are the objects in terms of which the Cvetković–Rowlinson conjecture and all the lemmas of Section 2 are stated.
--
--   **Formalization Note** Outerplanarity is topological, built on the published `RobertsonSeymour1986.GM5.PlaneDrawing`; it is not replaced by a forbidden-minor characterization. Because the drawing of a finite graph is compact, its complement has exactly one unbounded component, which is the outer face. A vertex point lies on the drawing, so membership in the closure of the outer face is the same as membership in its boundary. The fan lives on the vertex type $\mathrm{Fin}\,1 \sqcup \mathrm{Fin}(n-1)$; "$G$ is $K_1 + P_{n-1}$" is expressed elsewhere as a graph isomorphism. The paper's $e(X,Y)$ is used for disjoint $X$, $Y$, where the definition agrees with it.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, pp. 3–6, §1.2 (notation) and §2 (standing setting, p. 5; Figure 1, p. 6)

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_RobertsonSeymour1986_GM5_PlaneDrawing

namespace TaitTobin.Outerplanar

open RobertsonSeymour1986.GM5 WangKangXue.SpectralTuran

/-- The point set of a plane drawing: the vertex points together with the images of the edge
arcs. -/
def drawingImage {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G) : Set (ℝ × ℝ) :=
  Set.range D.vertex ∪ ⋃ (v : V) (w : V) (h : G.Adj v w), Set.range (D.arc h)

/-- The outer face of a plane drawing: the points of the plane off the drawing whose connected
component in the complement of the drawing is unbounded. -/
def outerFace {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G) : Set (ℝ × ℝ) :=
  {p | p ∉ drawingImage D ∧ ¬ Bornology.IsBounded (connectedComponentIn (drawingImage D)ᶜ p)}

/-- `G` is outerplanar: it has a plane drawing in which every vertex lies on the boundary of the
outer face (equivalently, in its closure, since a vertex point lies on the drawing). -/
def IsOuterplanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ D : PlaneDrawing G, ∀ v : V, D.vertex v ∈ closure (outerFace D)

/-- The join `G + H`: the disjoint union of `G` and `H` plus every edge between the two sides. -/
def join {α β : Type} (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α ⊕ β) where
  Adj
    | .inl a, .inl a' => G.Adj a a'
    | .inr b, .inr b' => H.Adj b b'
    | _, _ => True
  symm := ⟨fun u w h => by
    cases u <;> cases w <;> simp_all [SimpleGraph.adj_comm]⟩
  loopless := ⟨fun u h => by
    cases u <;> simp_all⟩

/-- `G` has property `P` and maximum spectral radius among all graphs on `Fin n` with `P`. -/
def IsSpecMax {n : ℕ} (P : SimpleGraph (Fin n) → Prop) (G : SimpleGraph (Fin n)) : Prop :=
  P G ∧ ∀ G' : SimpleGraph (Fin n), P G' → specRad G' ≤ specRad G

open Classical in
/-- `e(X)`: the number of edges of `G` with both endpoints in `X`. -/
noncomputable def eIn {V : Type} [Fintype V] (G : SimpleGraph V) (X : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ X)).card

open Classical in
/-- `e(X, Y)`: the number of edges of `G` with one endpoint in `X` and the other in `Y`
(the paper's `e(X, Y)` for disjoint `X`, `Y`; each edge is counted once). -/
noncomputable def eBetween {V : Type} [Fintype V] (G : SimpleGraph V) (X Y : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∃ a ∈ X, ∃ b ∈ Y, e = s(a, b))).card

/-- The fan `K₁ + Pₙ₋₁` (Figure 1, p. 6): one hub joined to every vertex of a path on `n - 1`
vertices. -/
def fan (n : ℕ) : SimpleGraph (Fin 1 ⊕ Fin (n - 1)) :=
  join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph (n - 1))

end TaitTobin.Outerplanar


