-- Prove2me | Definitions.Def_RamseyLST_Main_RamseySpanningTree
-- name    : RamseyLST_Main_RamseySpanningTree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:07:31.437476+00:00
-- url     : https://prove2.me/theorems/2162a52a-ce71-41bc-ac92-51ffb72955c2
-- title:
--   Spanning trees, stretch, diameter stretch and (weighted / strong) Ramsey spanning trees with a candidate core
-- statement:
--   Let $G=(V,E,\ell)$ be a weighted graph with positive edge lengths, and $d_G(u,v)\in[0,\infty]$ its shortest-path distance (the reused definition `ARTreeCover.WGraph`).
--
--   A **spanning tree** $T$ of $G$ is a subgraph of $G$ on all of $V$ which is a tree; it carries the edge lengths of $G$, and $d_T$ denotes its shortest-path distance. The **diameter** of $G$ is $\operatorname{diam}(G)=\max_{u,v}d_G(u,v)$, and $T$ has **diameter stretch at most $C_D$** if $\operatorname{diam}(T)\le C_D\operatorname{diam}(G)$.
--
--   For a set $Z\subseteq V$ (the **core**) and $\alpha\ge1$, the **stretch bound** is
--
--   $$d_T(x,y)\le\alpha\,d_G(x,y)$$
--
--   for every $x\in Z$ and every $y\in Z$ (non-strong) or every $y\in V$ (strong).
--
--   For a **candidate core** $A\subseteq V$, $(T,Z)$ is a (strong) **$(\alpha,\psi)$-Ramsey spanning tree with candidate core $A$** if $Z\subseteq A$, $|Z|\ge|A|^{\psi}$ and the (strong) stretch bound holds. Given a weight function $w:A\to\mathbb R_{\ge0}$, it is a **weighted** (strong) $(\alpha,\psi)$-Ramsey spanning tree with respect to $w$ if $Z\subseteq A$, $\sum_{x\in Z}w(x)^{\psi}\ge\big(\sum_{a\in A}w(a)\big)^{\psi}$ and the (strong) stretch bound holds. It is an $(\alpha,\psi,C_D)$-Ramsey spanning tree when, in addition, its diameter stretch is at most $C_D$.
--
--   These notions (Definitions 1–2) are the objects of the goal, Corollary 10, Assumption 1 and Theorem 25. Non-contractivity, which Definition 2 requires of a Ramsey embedding, holds for every spanning tree, since $T$ is a subgraph of $G$.
--
--   **Formalization Note** Distances are in $[0,\infty]$ (`ℝ≥0∞`); on a connected graph they are finite, and the stretch bound is compared in `ℝ≥0∞` as $d_T(x,y)\le \mathrm{ofReal}(\alpha)\cdot d_G(x,y)$. `rdist` is the real value of $d_G$. Powers are `Real.rpow`, for which $x^0=1$ also at $x=0$. The core-size requirements are imposed only for a non-empty candidate core $A$: for $A=\emptyset$ the paper notes that the requirement "holds trivially with an empty core" (p. 56), while `Real.rpow` would make $0\ge0^0=1$ false. A weight function is a function on $V$ of which only the values on $A$ are used.
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), pp. 8–10 (PDF 12–14), §2 and Definitions 1–2

import Mathlib
import Definitions.Def_ARTreeCover_WGraph

open scoped ENNReal

namespace RamseyLST.Main

open ARTreeCover

/-- The shortest-path distance `d_G(u, v)` as a real number (finite on a connected graph). -/
noncomputable def rdist {V : Type} (G : WGraph V) (u v : V) : ℝ := (G.dist u v).toReal

/-- A spanning tree of the weighted graph `G` (Definition 1, p. 9): a subgraph `T ≤ G` on all
of `V` which is a tree, carrying the edge lengths of `G`. -/
structure SpanningTree {V : Type} (G : WGraph V) where
  /-- The edge set of the tree. -/
  tree : SimpleGraph V
  /-- Every edge of the tree is an edge of `G`. -/
  le : tree ≤ G.graph
  /-- It is a tree (connected and acyclic). -/
  isTree : tree.IsTree

/-- The tree `T` as a weighted graph, with the edge lengths of `G`. -/
def SpanningTree.toWGraph {V : Type} {G : WGraph V} (T : SpanningTree G) : WGraph V where
  graph := T.tree
  w := G.w
  w_pos := fun e he => G.w_pos e (SimpleGraph.edgeSet_mono T.le he)

/-- `d_T`, the shortest-path metric of the spanning tree `T` with the edge lengths of `G`. -/
noncomputable def SpanningTree.dist {V : Type} {G : WGraph V} (T : SpanningTree G) (u v : V) :
    ℝ≥0∞ :=
  T.toWGraph.dist u v

/-- The diameter `diam(G) = max_{u, v} d_G(u, v)`, in `[0, ∞]`. -/
noncomputable def diamE {V : Type} (G : WGraph V) : ℝ≥0∞ := ⨆ u, ⨆ v, G.dist u v

/-- Diameter stretch at most `C_D` (Definitions 1–2): `diam_T(V) ≤ C_D · diam_G(V)`. -/
def DiamStretchLe {V : Type} (G : WGraph V) (T : SpanningTree G) (CD : ℝ) : Prop :=
  diamE T.toWGraph ≤ ENNReal.ofReal CD * diamE G

/-- The stretch requirement of Definition 2 with distortion `α`: `d_T(x, y) ≤ α · d_G(x, y)` for
every `x ∈ Z` and every `y ∈ Z` (non-strong, `strong = false`) or every vertex `y`
(strong, `strong = true`). -/
def StretchBound {V : Type} (strong : Bool) (G : WGraph V) (T : SpanningTree G) (Z : Finset V)
    (α : ℝ) : Prop :=
  ∀ x ∈ Z, ∀ y : V, (strong = true ∨ y ∈ Z) → T.dist x y ≤ ENNReal.ofReal α * G.dist x y

/-- Definition 2 (pp. 9–10): `(T, Z)` is a (strong, if `strong = true`) `(α, ψ)`-Ramsey spanning
tree of `G` with candidate core `A`: `Z ⊆ A`, `|Z| ≥ |A|^ψ` (required when `A ≠ ∅`), and the
stretch bound. -/
def IsRamseySpanningTree {V : Type} (strong : Bool) (G : WGraph V) (T : SpanningTree G)
    (A Z : Finset V) (α ψ : ℝ) : Prop :=
  Z ⊆ A ∧ (A.Nonempty → (A.card : ℝ) ^ ψ ≤ (Z.card : ℝ)) ∧ StretchBound strong G T Z α

/-- Definition 2 (pp. 9–10), weighted form: `(T, Z)` is a weighted (strong, if `strong = true`)
`(α, ψ)`-Ramsey spanning tree of `G` with respect to `w : A → ℝ≥0`: `Z ⊆ A`,
`∑_{x ∈ Z} w(x)^ψ ≥ (w(A))^ψ` (required when `A ≠ ∅`), and the stretch bound. Only the values
of `w` on `A` matter. -/
def IsWeightedRamseySpanningTree {V : Type} (strong : Bool) (G : WGraph V) (T : SpanningTree G)
    (A : Finset V) (w : V → ℝ) (Z : Finset V) (α ψ : ℝ) : Prop :=
  Z ⊆ A ∧ (A.Nonempty → (∑ a ∈ A, w a) ^ ψ ≤ ∑ z ∈ Z, (w z) ^ ψ) ∧
    StretchBound strong G T Z α

end RamseyLST.Main


