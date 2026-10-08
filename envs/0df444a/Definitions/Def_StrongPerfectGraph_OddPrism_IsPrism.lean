-- Prove2me | Definitions.Def_StrongPerfectGraph_OddPrism_IsPrism
-- name    : StrongPerfectGraph_OddPrism_IsPrism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T05:46:08.056543+00:00
-- url     : https://prove2.me/theorems/56c22937-112d-4601-ab53-834e7571e7e8
-- title:
--   Prisms; even, odd and long prisms
-- statement:
--   A **prism** is a graph consisting of two vertex-disjoint triangles $\{a_1,a_2,a_3\}$, $\{b_1,b_2,b_3\}$ and three paths $P_1,P_2,P_3$, where each $P_i$ has ends $a_i,b_i$, and for $1\le i<j\le 3$ the only edges between $V(P_i)$ and $V(P_j)$ are $a_ia_j$ and $b_ib_j$. The prism is **long** if at least one of the three paths has length $>1$. It is **even** if all three paths have even length, and **odd** otherwise.
--
--   $G$ **contains** an even prism (a long odd prism) if some induced subgraph of $G$ is one.
--
--   In a Berge graph the three paths of a prism have the same parity (7.2 of the paper), so a long odd prism has three odd paths, at least one of them of length at least $3$.
--
--   **Formalization Note** Three lists $p_1,p_2,p_3$ of vertices of $G$ *form a prism* when each is an induced path of $G$ of length at least $1$ (so $a_i\neq b_i$ and the triangles are disjoint), the three are vertex-disjoint, and for $i\neq j$ a vertex $x$ of $p_i$ and $y$ of $p_j$ are adjacent exactly when both are first vertices or both are last vertices. The union of the three paths then induces a prism, and every induced prism arises this way.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 93 (prism, long prism) and p. 119 (even and odd prism)

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge

namespace StrongPerfectGraph.OddPrism

/-- The paths `p₁, p₂, p₃` of `G` **form a prism** (p. 93): each `pᵢ` is a path of `G` from
`aᵢ` (its first vertex) to `bᵢ` (its last vertex) of length at least one, the three paths are
vertex-disjoint, and for `i ≠ j` the only edges between `V(pᵢ)` and `V(pⱼ)` are `aᵢaⱼ` and
`bᵢbⱼ` (all of which are present). So `{a₁, a₂, a₃}` and `{b₁, b₂, b₃}` are vertex-disjoint
triangles and the union of the three paths induces a prism in `G`. -/
def IsPrism {V : Type*} (G : SimpleGraph V) (p₁ p₂ p₃ : List V) : Prop :=
  let P : Fin 3 → List V := ![p₁, p₂, p₃]
  (∀ i, IsInducedPath G (P i) ∧ 1 ≤ (P i).length - 1) ∧
  (∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j) ∧
  (∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j,
    G.Adj x y ↔
      ((P i).head? = some x ∧ (P j).head? = some y) ∨
      ((P i).getLast? = some x ∧ (P j).getLast? = some y))

/-- A prism is **even** (p. 119) if its three paths have even length; it is **odd** otherwise. -/
def IsEvenPrism {V : Type*} (G : SimpleGraph V) (p₁ p₂ p₃ : List V) : Prop :=
  IsPrism G p₁ p₂ p₃ ∧
    Even (p₁.length - 1) ∧ Even (p₂.length - 1) ∧ Even (p₃.length - 1)

/-- A **long odd prism**: a prism that is long (p. 93: at least one of its paths has length
`> 1`) and odd (p. 119: not all three paths have even length). -/
def IsLongOddPrism {V : Type*} (G : SimpleGraph V) (p₁ p₂ p₃ : List V) : Prop :=
  IsPrism G p₁ p₂ p₃ ∧
    (1 < p₁.length - 1 ∨ 1 < p₂.length - 1 ∨ 1 < p₃.length - 1) ∧
    ¬ (Even (p₁.length - 1) ∧ Even (p₂.length - 1) ∧ Even (p₃.length - 1))

/-- `G` **contains an even prism**: some induced subgraph of `G` is an even prism. -/
def ContainsEvenPrism {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ p₁ p₂ p₃ : List V, IsEvenPrism G p₁ p₂ p₃

/-- `G` **contains a long odd prism** as an induced subgraph. -/
def ContainsLongOddPrism {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ p₁ p₂ p₃ : List V, IsLongOddPrism G p₁ p₂ p₃

end StrongPerfectGraph.OddPrism


