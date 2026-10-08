-- Prove2me | Definitions.Def_Menger27_Graphs_Separation
-- name    : Menger27_Graphs_Separation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:08:42.23298+00:00
-- url     : https://prove2.me/theorems/ce5dc88a-41d8-47d1-8708-b0fcf17025d3
-- title:
--   pp. 99–100 — a vertex set separating P and Q; n-point connectedness between P and Q; n disjoint P–Q paths
-- statement:
--   Let $G$ be a simple graph on a vertex set $V$, and let $P, Q \subseteq V$ be finite sets of vertices. This file fixes the three notions in which Menger states Satz β and Satz δ.
--
--   1. **Separation** (p. 99). A finite set $S \subseteq V$ *separates* $P$ and $Q$ in $G$ if every walk of $G$ that starts at a vertex of $P$ and ends at a vertex of $Q$ passes through a vertex of $S$:
--   $$\forall x \in P,\ \forall y \in Q,\ \forall \text{ walks } x = v_0, v_1, \dots, v_k = y \text{ of } G:\quad \{v_0, \dots, v_k\} \cap S \neq \emptyset .$$
--   The set $S$ may contain vertices of $P$ and of $Q$. Menger's wording is "eine Menge, so dass $R_k - E$ in zwei relativ abgeschlossene, zu einander fremde Teile zerfällt, von denen der eine die Menge $B_k - E.B_k$, der andere die Menge $B_{k+1} - E.B_{k+1}$ enthält": after deleting $S$, no vertex of $P - S$ is joined to a vertex of $Q - S$.
--
--   2. **$n$-point connectedness** (p. 100, "n-punktig zusammenhängend"). $G$ is *$n$-point connected between $P$ and $Q$* if no set of fewer than $n$ vertices separates $P$ and $Q$, that is, $n \le |S|$ for every separating set $S$.
--
--   3. **$n$ pairwise disjoint paths between $P$ and $Q$** (p. 100, Satz β: "n paarweise fremde Bögen, von denen jeder einen Punkt von P und einen Punkt von Q verbindet"). There are paths $W_1, \dots, W_n$ of $G$, each starting at a vertex of $P$ and ending at a vertex of $Q$, whose vertex sets are pairwise disjoint. Disjointness includes the end vertices: two of the paths may not share a start or an end. Inner vertices of a path may lie in $P$ or $Q$.
--
--   These three notions are the vocabulary of Menger's theorem: Satz δ says that $n$-point connectedness between disjoint $P$ and $Q$ yields $n$ disjoint $P$–$Q$ paths.
--
--   **Formalization Note.** Menger works with a *gewöhnlich eindimensionaler Raum* $K$, a finite union of arcs any two of which meet at most in end points (p. 101). This mission reads $K$ as a finite simple graph: the vertices are a finite set containing the points of $P \cup Q$ and all end and branch points of $K$ (Menger's *punktförmige Stücke*), the edges are the arcs between them, subdivided so that there are no loops and no parallel arcs. Subdivision vertices, parallel arcs and loops change neither which vertex sets separate $P$ and $Q$ nor the largest number of disjoint $P$–$Q$ paths, and a separating point inside an open arc can be replaced by an end vertex of that arc, so separating sets may be taken to consist of vertices. Separation is stated through walks instead of through a splitting of $G - S$ into two closed parts; in a graph the two are equivalent. The disjointness of $P$ and $Q$ ("zwischen den beiden *fremden* … Teilmengen") is not built into the definition: every theorem of the mission carries it as the hypothesis `Disjoint P Q`. Paths are `SimpleGraph.Walk`s with `IsPath`; disjointness is `List.Disjoint` of the vertex lists.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), pp. 99–100, definition of separating sets (p. 99) and of 'n-punktig zusammenhängend' (p. 100), Satz β (p. 100)

import Mathlib

namespace Menger27.Graphs

/-- `Separates G P Q S` (Menger 1927, p. 99): the vertex set `S` separates `P` and `Q` in `G`,
i.e. every walk of `G` from a vertex of `P` to a vertex of `Q` passes through a vertex of `S`.
`S` may contain vertices of `P` and of `Q`. -/
def Separates {V : Type*} (G : SimpleGraph V) (P Q S : Finset V) : Prop :=
  ∀ x ∈ P, ∀ y ∈ Q, ∀ w : G.Walk x y, ∃ v ∈ w.support, v ∈ S

/-- `NPointConnected G P Q n` (Menger 1927, p. 100, "n-punktig zusammenhängend"): no set of fewer
than `n` vertices separates `P` and `Q` in `G`. -/
def NPointConnected {V : Type*} (G : SimpleGraph V) (P Q : Finset V) (n : ℕ) : Prop :=
  ∀ S : Finset V, Separates G P Q S → n ≤ S.card

/-- `HasDisjointPaths G P Q n` (Menger 1927, p. 100, Satz β): `G` contains `n` pairwise
vertex-disjoint paths (endpoints included), each starting at a vertex of `P` and ending at a
vertex of `Q`. -/
def HasDisjointPaths {V : Type*} (G : SimpleGraph V) (P Q : Finset V) (n : ℕ) : Prop :=
  ∃ (a b : Fin n → V) (w : ∀ i, G.Walk (a i) (b i)),
    (∀ i, a i ∈ P ∧ b i ∈ Q ∧ (w i).IsPath) ∧
    ∀ i j, i ≠ j → List.Disjoint (w i).support (w j).support

end Menger27.Graphs


