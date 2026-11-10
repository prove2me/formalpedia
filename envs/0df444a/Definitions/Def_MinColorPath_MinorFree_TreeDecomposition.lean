-- Prove2me | Definitions.Def_MinColorPath_MinorFree_TreeDecomposition
-- name    : MinColorPath_MinorFree_TreeDecomposition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:11:47.514124+00:00
-- url     : https://prove2.me/theorems/37a9e189-4232-474a-a365-1d180fb5f266
-- title:
--   Rooted binary tree decompositions, γ(x), x-segments, chromatic width and crossing number
-- statement:
--   A **tree decomposition** $(T,\beta)$ of a graph $D$ is a tree $T$ with bags $\beta(x)\subseteq V(D)$ covering $V(D)$ and every edge, such that the nodes whose bags contain a fixed vertex form a subtree; $T$ is always **rooted**, and the decomposition is **binary** if every node has at most two children. For a node $x$, $T_x$ is the subtree rooted at $x$ and
--   $$\gamma(x)=\bigcup_{y\in V(T_x)}\beta(y).$$
--   For a path $\pi$, the **$x$-segments** of $\pi$ are the connected components of $\pi[\gamma(x)]$; a segment is **trivial** if its vertices lie in $\beta(x)$. The **crossing number** of $\pi$ in $(T,\beta)$ is $\max_x k_x$ with $k_x$ the number of nontrivial $x$-segments. For a colored graph the **chromatic width** is $\max_x|\mathrm{cl}(\beta(x))|$.
--
--   **Formalization Note.** `RTD D` bundles a finite node type, the tree `t`, a `root`, the bags and the published `IsTreeDecomposition` (whose path condition is equivalent to the subtree condition). `InSub x y` says the root-to-`y` path passes through `x`; `children x` are the neighbours of `x` in $T_x$; `height x` is the largest distance from `x` to a node of $T_x$. A path enters as its vertex list `π.support`; an $x$-segment is a maximal run `[i, j]` of consecutive positions inside $\gamma(x)$ (`IsSeg`), membership being `mem` (plain membership for a decomposition of $G$, `baseIn` for a decomposition of a diagram). `pathCrossing`, `diagWidth`, `TerminalsInBags` and `extraUncolored` ($|\beta(x)\cap V_0(\mathcal G)\setminus\{s,t\}|$) specialise these notions to diagrams of a path.
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), pp. 18–19, 'Tree decomposition, chromatic width, and crossing number'

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_MinColorPath_MinorFree_Diagram

set_option autoImplicit false

/-!
# Rooted binary tree decompositions, x-segments, chromatic width, crossing number (pp. 18–19)

Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, *Algorithms for Min-Color Path with Bounded
Color-Degree* (STOC 2027 submission), pp. 18–19, "Tree decomposition, chromatic width, and
crossing number".

Conventions.
* A tree decomposition is the published `RobertsonSeymour1986.GM5.IsTreeDecomposition` (tree,
  cover, edges, path condition (iii), equivalent to the paper's connected-subtree condition) on a
  finite node type, together with a root ("we always consider T as a rooted tree", p. 18).
* `T_x` is the set of nodes `y` whose path from the root passes through `x`; `γ(x)` is the union
  of the bags of `T_x`; the children of `x` are its neighbours in `T_x`; the height of `x` is the
  largest distance from `x` to a node of `T_x`; binary means at most two children per node.
* A path `π` enters as its vertex list `π.support` (from the `s`-side). Its `x`-segments, the
  connected components of `π[γ(x)]`, are the maximal runs `[i, j]` of consecutive list positions
  whose vertices lie in `γ(x)`; positions are 0-based. Since `π` is a path, its edges are exactly
  the consecutive pairs, so these runs are the components.
* Membership of a vertex of the path in a bag is a parameter `mem`: plain membership for a tree
  decomposition of `G` itself (Lemma 3.4), membership of the base vertex for a tree decomposition
  of a diagram (`baseIn`).
-/

namespace MinColorPath.MinorFree

noncomputable section

open Classical

/-- A rooted tree decomposition `(T, β)` of a graph `D` on `W`, with a finite node type. -/
structure RTD {W : Type} [DecidableEq W] (D : SimpleGraph W) where
  /-- The node type of the tree `T`. -/
  T : Type
  [instFintype : Fintype T]
  [instDecEq : DecidableEq T]
  /-- The tree `T`. -/
  t : SimpleGraph T
  /-- The root of `T`. -/
  root : T
  /-- The bags `β(x)`. -/
  bag : T → Finset W
  isTD : RobertsonSeymour1986.GM5.IsTreeDecomposition D t bag

attribute [instance] RTD.instFintype RTD.instDecEq

namespace RTD

variable {W : Type} [DecidableEq W] {D : SimpleGraph W} (𝒯 : RTD D)

/-- `y ∈ V(T_x)`: the path from the root to `y` passes through `x`. -/
def InSub (x y : 𝒯.T) : Prop :=
  ∃ p : 𝒯.t.Walk 𝒯.root y, p.IsPath ∧ x ∈ p.support

/-- The node set of the subtree `T_x` rooted at `x`. -/
def subtree (x : 𝒯.T) : Finset 𝒯.T := Finset.univ.filter (𝒯.InSub x)

/-- `γ(x) = ⋃_{y ∈ V(T_x)} β(y)`. -/
def gamma (x : 𝒯.T) : Finset W := (𝒯.subtree x).biUnion 𝒯.bag

/-- The children of `x`: its neighbours in `T` that lie in `T_x`. -/
def children (x : 𝒯.T) : Finset 𝒯.T :=
  Finset.univ.filter fun y => 𝒯.t.Adj x y ∧ 𝒯.InSub x y

/-- `(T, β)` is binary: every node has at most two children. -/
def IsBinary : Prop := ∀ x, (𝒯.children x).card ≤ 2

/-- The height of `x` in `T`: the largest distance from `x` to a node of `T_x` (leaves have
height `0`). -/
def height (x : 𝒯.T) : ℕ := (𝒯.subtree x).sup fun y => 𝒯.t.dist x y

/-- The chromatic width `max_x |cl'(β(x))|` for a coloring `clD` of the vertices of `D`
(p. 19). -/
def chromWidth {C : Type} (clD : W → Finset C) : ℕ :=
  Finset.univ.sup fun x => (colSet clD (𝒯.bag x)).card

end RTD

/-- `[i, j]` is a maximal run of consecutive positions of the list `l` whose vertices satisfy `M`:
a connected component of `π[M]` for the path `π` with vertex list `l`. -/
def IsSeg {V : Type} (M : V → Prop) (l : List V) (i j : Fin l.length) : Prop :=
  i ≤ j ∧ (∀ k : Fin l.length, i ≤ k → k ≤ j → M (l.get k)) ∧
    (∀ k : Fin l.length, k.val + 1 = i.val → ¬ M (l.get k)) ∧
    (∀ k : Fin l.length, k.val = j.val + 1 → ¬ M (l.get k))

/-- The run `[i, j]` lies inside `Mβ` (a trivial segment when `Mβ` is the bag of `x`). -/
def IsInside {V : Type} (Mβ : V → Prop) (l : List V) (i j : Fin l.length) : Prop :=
  ∀ k : Fin l.length, i ≤ k → k ≤ j → Mβ (l.get k)

/-- The `x`-segments of the path with vertex list `l` in `𝒯`: maximal runs inside `γ(x)`. -/
def RTD.IsSegment {W V : Type} [DecidableEq W] {D : SimpleGraph W} (𝒯 : RTD D)
    (mem : Finset W → V → Prop) (l : List V) (x : 𝒯.T) (i j : Fin l.length) : Prop :=
  IsSeg (mem (𝒯.gamma x)) l i j

/-- `k_x`, the number of nontrivial `x`-segments (segments not contained in `β(x)`). -/
def RTD.numNontrivial {W V : Type} [DecidableEq W] {D : SimpleGraph W} (𝒯 : RTD D)
    (mem : Finset W → V → Prop) (l : List V) (x : 𝒯.T) : ℕ :=
  (Finset.univ.filter fun ij : Fin l.length × Fin l.length =>
    𝒯.IsSegment mem l x ij.1 ij.2 ∧ ¬ IsInside (mem (𝒯.bag x)) l ij.1 ij.2).card

/-- The crossing number `max_x k_x` of the path with vertex list `l` in `𝒯` (p. 19). -/
def RTD.crossing {W V : Type} [DecidableEq W] {D : SimpleGraph W} (𝒯 : RTD D)
    (mem : Finset W → V → Prop) (l : List V) : ℕ :=
  Finset.univ.sup fun x => 𝒯.numNontrivial mem l x

variable {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]

/-- The `d`-diagram graph of a walk `π` (used for paths): the diagram of `π.toSubgraph`. -/
abbrev pathDiag {G : SimpleGraph V} (cl : V → Finset C) (d : ℕ) {s t : V} (π : G.Walk s t) :
    SimpleGraph (DV cl π.toSubgraph) :=
  diagGraph cl d π.toSubgraph

/-- The crossing number of the path `π` in a tree decomposition of one of its diagrams. -/
def pathCrossing {G : SimpleGraph V} {cl : V → Finset C} {d : ℕ} {s t : V} {π : G.Walk s t}
    (𝒯 : RTD (pathDiag cl d π)) : ℕ :=
  𝒯.crossing baseIn π.support

/-- The chromatic width of a tree decomposition of a diagram, with the coloring `cl'`. -/
def diagWidth {G : SimpleGraph V} {cl : V → Finset C} {H : G.Subgraph} {D : SimpleGraph (DV cl H)}
    (𝒯 : RTD D) : ℕ :=
  𝒯.chromWidth (diagCl cl H)

/-- Both terminals lie in every bag: `s, t ∈ β(x)` for all `x ∈ V(T)`. -/
def TerminalsInBags {G : SimpleGraph V} {cl : V → Finset C} {H : G.Subgraph}
    {D : SimpleGraph (DV cl H)} (𝒯 : RTD D) (s t : V) : Prop :=
  ∀ x, baseIn (𝒯.bag x) s ∧ baseIn (𝒯.bag x) t

/-- `|β(x) ∩ V_0(G) \ {s, t}|`: the uncolored base vertices of the bag other than `s, t`. -/
def extraUncolored {G : SimpleGraph V} {cl : V → Finset C} {H : G.Subgraph}
    {D : SimpleGraph (DV cl H)} (𝒯 : RTD D) (s t : V) (x : 𝒯.T) : ℕ :=
  ((subVerts H).filter fun v => baseIn (𝒯.bag x) v ∧ cl v = ∅ ∧ v ≠ s ∧ v ≠ t).card

end

end MinColorPath.MinorFree


