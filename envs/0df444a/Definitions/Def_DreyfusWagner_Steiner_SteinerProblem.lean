-- Prove2me | Definitions.Def_DreyfusWagner_Steiner_SteinerProblem
-- name    : DreyfusWagner_Steiner_SteinerProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:03:04.467174+00:00
-- url     : https://prove2.me/theorems/e262fc83-a966-447f-8b1b-fb439a5b6aaf
-- title:
--   The Steiner problem in a graph: arc length, connecting arc sets, Steiner trees, Steiner length, shortest-path length
-- statement:
--   Let $G = (N, A)$ be a finite undirected graph with node set $N$ and arc set $A$, and let each arc $a \in A$ carry a length $|a|$. For a finite set $S$ of arcs write
--   $$|S| = \sum_{s \in S} |s|$$
--   for its total length. A set $S$ of arcs **connects** a node set $X \subseteq N$ if all members of $X$ are joined by paths composed only of arcs in $S$.
--
--   A **Steiner path** (or **Steiner tree**) connecting $X$ in $G$ is a set $S \subseteq A$ that connects $X$ and has minimum total length $|S|$ among all subsets of $A$ that connect $X$. The **Steiner length** of $X$ is that minimum,
--   $$\operatorname{St}(X) = \min\{\, |S| : S \subseteq A,\ S \text{ connects } X \,\},$$
--   taken in $\mathbb{R} \cup \{+\infty\}$, with the value $+\infty$ when no subset of $A$ connects $X$. If $X$ is a single node, the empty arc set connects it and $\operatorname{St}(X) = 0$.
--
--   Finally, $D(i,j)$ denotes the length of the shortest path in $G$ from node $i$ to node $j$: the minimum, over all paths from $i$ to $j$ in $G$, of the sum of the lengths of the arcs of the path, again in $\mathbb{R} \cup \{+\infty\}$. In particular $D(i,i) = 0$.
--
--   These are the objects of the Steiner problem of Dreyfus and Wagner: given $Y \subseteq N$, find a set $S \subseteq A$ that connects $Y$ with $|S|$ minimum.
--
--   **Formalization Note** Nodes form a finite type `V`, the graph is a `SimpleGraph V` (at most one arc between two nodes, no loops), arcs are unordered pairs `Sym2 V`, and lengths are a function `ℓ : Sym2 V → ℝ`. "Connected by paths composed only of arcs in $S$" is reachability in the graph `SimpleGraph.fromEdgeSet S`. The Steiner length and $D(i,j)$ are `Finset.inf` into `WithTop ℝ`, whose top element `⊤` plays the role of $+\infty$ (the value of a minimum over an empty set). $D(i,j)$ ranges over paths (walks without repeated nodes) of $G$; every path has fewer than $|N|$ arcs, so the minimum over walks of length less than $|N|$ that are paths covers all paths. Positivity of lengths and connectivity of $G$ are not built into these definitions; the theorems assume them.
-- source:
--   Dreyfus, Wagner, The Steiner Problem in Graphs, Networks 1 (1971), p. 195, §1 (conditions (1), (2)) and Abstract; p. 196, §1 (one-node case); p. 202, §4 (D(i,j))

import Mathlib

namespace DreyfusWagner.Steiner

variable {V : Type*}

/-- Total length `|S| = ∑_{s ∈ S} |s|` of a finite set `S` of arcs, where `ℓ` gives the length
of each arc (Dreyfus–Wagner 1971, §1, p. 195, condition (2)). -/
def arcLength (ℓ : Sym2 V → ℝ) (S : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ S, ℓ e

/-- The arc set `S` connects the node set `X`: any two members of `X` are joined by a path
composed only of arcs in `S` (Dreyfus–Wagner 1971, §1, p. 195, condition (1)). -/
def Connects (S : Finset (Sym2 V)) (X : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).Reachable x y

/-- `S` is a Steiner path (Steiner tree) connecting `X` in `G` with arc lengths `ℓ`: `S` is a set
of arcs of `G` that connects `X` and has minimum total length among all such arc sets
(Dreyfus–Wagner 1971, §1, pp. 195–196). -/
def IsSteinerTree [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ℓ : Sym2 V → ℝ) (X : Finset V) (S : Finset (Sym2 V)) : Prop :=
  S ⊆ G.edgeFinset ∧ Connects S X ∧
    ∀ S' ⊆ G.edgeFinset, Connects S' X → arcLength ℓ S ≤ arcLength ℓ S'

open Classical in
/-- The length of the Steiner path connecting `X` in `G`: the minimum of `|S|` over all arc sets
`S ⊆ A` connecting `X`, as an element of `WithTop ℝ` (it is `⊤ = ∞` exactly when no arc set of `G`
connects `X`). -/
noncomputable def steinerLength [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ) (X : Finset V) : WithTop ℝ :=
  (G.edgeFinset.powerset.filter (fun S => Connects S X)).inf
    (fun S => ((arcLength ℓ S : ℝ) : WithTop ℝ))

open Classical in
/-- `D(i,j)`: the length of the shortest path in `G` from `i` to `j` (Dreyfus–Wagner 1971, §4,
p. 202), i.e. the minimum of the sum of the arc lengths along a path `i → j` of `G`, as an
element of `WithTop ℝ` (`⊤ = ∞` when there is no such path). Every path of `G` has fewer than
`Fintype.card V` arcs, so the minimum ranges over all paths from `i` to `j`. -/
noncomputable def pathDist [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ℓ : Sym2 V → ℝ) (i j : V) : WithTop ℝ :=
  (Finset.range (Fintype.card V)).inf fun n =>
    ((G.finsetWalkLength n i j).filter (fun p => p.IsPath)).inf
      fun p => (((p.edges.map ℓ).sum : ℝ) : WithTop ℝ)

end DreyfusWagner.Steiner


