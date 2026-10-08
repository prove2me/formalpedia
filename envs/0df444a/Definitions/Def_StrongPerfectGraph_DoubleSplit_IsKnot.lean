-- Prove2me | Definitions.Def_StrongPerfectGraph_DoubleSplit_IsKnot
-- name    : StrongPerfectGraph_DoubleSplit_IsKnot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:05:30.246398+00:00
-- url     : https://prove2.me/theorems/641b375a-e783-412f-8c57-7164838e1784
-- title:
--   Knots, local and resolving sets of a knot, attachments
-- statement:
--   Let $P_1, P_2$ be paths and $Q_1, Q_2$ antipaths of a graph $G$, pairwise disjoint, with ends labelled $a_i, b_i$ (of $P_i$) and $x_j, y_j$ (of $Q_j$). The quadruple $(P_1, P_2, Q_1, Q_2)$ is a **knot** in $G$ if
--
--   1. $P_1, P_2, Q_1, Q_2$ all have length $\ge 1$;
--   2. there are no edges between $P_1$ and $P_2$, and $Q_1$ is complete to $Q_2$;
--   3. for $(i, j) = (1,1), (1,2), (2,1)$ the only edges between $V(P_i)$ and $\{x_j, y_j\}$ are $a_ix_j$ and $b_iy_j$, and the only edges between $V(P_2)$ and $\{x_2, y_2\}$ are $a_2y_2$ and $b_2x_2$;
--   4. for $(i, j) = (1,1), (1,2), (2,1)$ the only nonedges between $V(Q_j)$ and $\{a_i, b_i\}$ are $a_iy_j$ and $b_ix_j$, and the only nonedges between $V(Q_2)$ and $\{a_2, b_2\}$ are $a_2x_2$ and $b_2y_2$.
--
--   The knot **induces** $K = G|(V(P_1) \cup V(P_2) \cup V(Q_1) \cup V(Q_2))$. A set $X \subseteq V(K)$ is **local** with respect to the knot if $X$ is disjoint from one of $V(P_1), V(P_2)$, includes neither of $V(Q_1), V(Q_2)$, and $X \cap (V(P_1) \cup V(P_2))$ is complete to $X \cap (V(Q_1) \cup V(Q_2))$. The set $X$ **resolves** the knot if $V(K) \setminus X$ is local with respect to the knot $(Q_1, Q_2, P_1, P_2)$ in $\overline{G}$. If $F$ is disjoint from $K$, a vertex of $K$ is an **attachment** of $F$ if it has a neighbour in $F$.
--
--   A degenerate appearance of $K_4$ is a knot, and by 9.1 the knots of Berge graphs are exactly these and their complements.
--
--   **Formalization Note** Paths and antipaths are lists, and the labelling of the ends is fixed by the lists: $a_i, b_i$ are the first and last vertices of $P_i$, $x_j, y_j$ those of $Q_j$. Condition 3–4 for $(i,j) = (2,2)$ is the pattern of the other three pairs with $Q_2$ reversed.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), pp. 107–108, §9, definition of knot, induces, local and resolves; p. 75, §5, definition of attachment

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath

namespace StrongPerfectGraph.DoubleSplit

/-- The adjacency pattern of a knot between a path `P` with ends `a = P.head`, `b = P.getLast`
and an antipath `Q` with ends `x = Q.head`, `y = Q.getLast` (p. 108): the only edges between
`V(P)` and `{x, y}` are `ax` and `by`, and the only nonedges between `V(Q)` and `{a, b}` are `ay`
and `bx`. For the pair `(P₂, Q₂)` the knot uses this pattern with `Q₂` reversed. -/
def KnotPattern {V : Type*} (G : SimpleGraph V) (P Q : List V) : Prop :=
  ∀ a b x y : V, P.head? = some a → P.getLast? = some b →
    Q.head? = some x → Q.getLast? = some y →
    (∀ u ∈ P, (G.Adj u x ↔ u = a) ∧ (G.Adj u y ↔ u = b)) ∧
    (∀ w ∈ Q, (¬ G.Adj a w ↔ w = y) ∧ (¬ G.Adj b w ↔ w = x))

/-- A **knot** `(P₁, P₂, Q₁, Q₂)` in `G` (pp. 107–108). `P₁, P₂` are paths and `Q₁, Q₂` antipaths,
each given as a list; the list fixes the labelling of the ends: `aᵢ, bᵢ` are the first and last
vertex of `Pᵢ`, and `xⱼ, yⱼ` the first and last vertex of `Qⱼ`. The four are pairwise disjoint and
have length at least one; there are no edges between `P₁` and `P₂` and `Q₁` is complete to `Q₂`;
for `(i, j) = (1,1), (1,2), (2,1)` the only edges between `V(Pᵢ)` and `{xⱼ, yⱼ}` are `aᵢxⱼ, bᵢyⱼ`
and the only nonedges between `V(Qⱼ)` and `{aᵢ, bᵢ}` are `aᵢyⱼ, bᵢxⱼ`; and the only edges between
`V(P₂)` and `{x₂, y₂}` are `a₂y₂, b₂x₂`, the only nonedges between `V(Q₂)` and `{a₂, b₂}` are
`a₂x₂, b₂y₂` (i.e. the same pattern with `Q₂` reversed). -/
def IsKnot {V : Type*} (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V) : Prop :=
  StrongPerfectGraph.Main.IsInducedPath G P₁ ∧ StrongPerfectGraph.Main.IsInducedPath G P₂ ∧ StrongPerfectGraph.Main.IsInducedPath Gᶜ Q₁ ∧ StrongPerfectGraph.Main.IsInducedPath Gᶜ Q₂ ∧
  (∀ v, v ∈ P₁ → v ∉ P₂ ∧ v ∉ Q₁ ∧ v ∉ Q₂) ∧
  (∀ v, v ∈ P₂ → v ∉ Q₁ ∧ v ∉ Q₂) ∧
  (∀ v, v ∈ Q₁ → v ∉ Q₂) ∧
  2 ≤ P₁.length ∧ 2 ≤ P₂.length ∧ 2 ≤ Q₁.length ∧ 2 ≤ Q₂.length ∧
  (∀ u ∈ P₁, ∀ v ∈ P₂, ¬ G.Adj u v) ∧
  (∀ u ∈ Q₁, ∀ v ∈ Q₂, G.Adj u v) ∧
  KnotPattern G P₁ Q₁ ∧ KnotPattern G P₁ Q₂ ∧ KnotPattern G P₂ Q₁ ∧
  KnotPattern G P₂ Q₂.reverse

/-- The vertex set `V(K) = V(P₁) ∪ V(P₂) ∪ V(Q₁) ∪ V(Q₂)` of the graph `K` induced by the knot. -/
def knotVerts {V : Type*} (P₁ P₂ Q₁ Q₂ : List V) : Set V :=
  {v | v ∈ P₁ ∨ v ∈ P₂ ∨ v ∈ Q₁ ∨ v ∈ Q₂}

/-- `X ⊆ V(K)` is **local** with respect to the knot `(P₁, P₂, Q₁, Q₂)` (p. 108): `X` is disjoint
from one of `V(P₁), V(P₂)`, includes neither of `V(Q₁), V(Q₂)`, and `X ∩ (V(P₁) ∪ V(P₂))` is
complete to `X ∩ (V(Q₁) ∪ V(Q₂))`. -/
def IsLocalForKnot {V : Type*} (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V) (X : Set V) : Prop :=
  X ⊆ knotVerts P₁ P₂ Q₁ Q₂ ∧
  ((∀ v ∈ P₁, v ∉ X) ∨ (∀ v ∈ P₂, v ∉ X)) ∧
  ¬ (∀ v ∈ Q₁, v ∈ X) ∧ ¬ (∀ v ∈ Q₂, v ∈ X) ∧
  ∀ u ∈ X, ∀ w ∈ X, (u ∈ P₁ ∨ u ∈ P₂) → (w ∈ Q₁ ∨ w ∈ Q₂) → G.Adj u w

/-- `X` **resolves** the knot `(P₁, P₂, Q₁, Q₂)` (p. 108): `V(K) \ X` is local with respect to the
knot `(Q₁, Q₂, P₁, P₂)` in the complement `G̅`. -/
def ResolvesKnot {V : Type*} (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V) (X : Set V) : Prop :=
  IsLocalForKnot Gᶜ Q₁ Q₂ P₁ P₂ (knotVerts P₁ P₂ Q₁ Q₂ \ X)

/-- The **attachments** of `F` in a vertex set `K` (p. 75): the vertices of `K` with a neighbour
in `F`. -/
def attachments {V : Type*} (G : SimpleGraph V) (K F : Set V) : Set V :=
  {v | v ∈ K ∧ ∃ f ∈ F, G.Adj v f}

end StrongPerfectGraph.DoubleSplit


