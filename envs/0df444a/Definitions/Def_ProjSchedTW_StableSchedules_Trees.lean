-- Prove2me | Definitions.Def_ProjSchedTW_StableSchedules_Trees
-- name    : ProjSchedTW_StableSchedules_Trees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T00:54:03.920572+00:00
-- url     : https://prove2.me/theorems/a5d35d70-bd8f-487e-8018-8d585588fb14
-- title:
--   Definition 2.3.2 and §3.2 (p. 216) — order-network weights, spanning trees and outtrees, tree equation systems
-- statement:
--   This file defines the network objects used to describe vertices by spanning trees.
--
--   1. **Order network** $N(O)$ (Definition 2.3.2). Take the project network $N$. For each pair $(i,j)$ of a strict order $O$, add the arc $\langle i,j\rangle$ with weight $p_i$. If $N$ already contains the arc $\langle i,j\rangle$ with weight $\delta_{ij}$, replace its weight by $\max(\delta_{ij},p_i)$. The arc set of $N(O)$ is $E\cup O$.
--   2. **Spanning tree** (p. 216). A set $E^G$ of arcs on the node set $V$ is a spanning tree if it has $|V|-1=n+1$ arcs and its underlying undirected graph is connected; this is a weakly connected directed graph with $m$ nodes and $m-1$ arcs. The tree is a **spanning outtree rooted at $0$** if, in addition, each path of the tree from $0$ to a node $j$ is directed from $0$ to $j$.
--   3. **Tree equation system.** For arc weights $w$, a schedule $S$ **uniquely solves** the system
--   $$S_0=0,\qquad S_j-S_i=w_{ij}\quad(\langle i,j\rangle\in E^G)$$
--   if $S$ satisfies it and every solution equals $S$.
--   4. **Walks** in $N$. A directed walk from $i$ to $j$ has as its length the sum of the weights $\delta$ of its arcs.
--
--   Proposition 3.2.16 and Theorem 3.2.18 characterize vertices of $\mathcal S_T$ and quasistable schedules through these objects.
--
--   **Formalization Note** A spanning tree is given by its arc set, a finset of ordered pairs. "Underlying undirected graph connected" uses Mathlib's `SimpleGraph.fromRel`. The outtree condition is stated as: every node is reachable from $0$ along tree arcs, which for a tree is equivalent to the book's condition. The walk length is an inductive predicate.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 30 (Definition 2.3.2), p. 216 (trees, outtrees, spanning trees), p. 217 (Proposition 3.2.16), p. 218 (Theorem 3.2.18), p. 8 (paths from node 0)

import Mathlib
import Definitions.Def_ProjSchedTW_StableSchedules_Project

namespace ProjSchedTW.StableSchedules

variable {n : ℕ} {K : Type}

/-- Definition 2.3.2 (p. 30): the arc weights of the order network `N(O)`. For a pair
`(i, j) ∈ O` the arc `⟨i, j⟩` has weight `p_i`, or `max(δ_ij, p_i)` if `N` already contains the
arc `⟨i, j⟩`; the other arcs of `N` keep their weight `δ_ij`. -/
noncomputable def orderWeight (P : Project n K) (O : Set (Fin (n + 2) × Fin (n + 2)))
    (i j : Fin (n + 2)) : ℤ := by
  classical
  exact if (i, j) ∈ O then (if (i, j) ∈ P.E then max (P.δ i j) (P.p i : ℤ) else (P.p i : ℤ))
    else P.δ i j

/-- Definition 2.3.2 (p. 30): the arc set of the order network `N(O)`, i.e. `E ∪ O`. -/
def orderArcs (P : Project n K) (O : Set (Fin (n + 2) × Fin (n + 2))) :
    Set (Fin (n + 2) × Fin (n + 2)) :=
  {e | e ∈ P.E ∨ e ∈ O}

/-- §3.2, p. 216: a set `E^G` of arcs on the node set `V` is (the arc set of) a spanning tree if
it has `|V| − 1 = n + 1` arcs and its underlying undirected graph is connected (a weakly
connected directed graph with `m` nodes and `m − 1` arcs). -/
def IsSpanningTree (EG : Finset (Fin (n + 2) × Fin (n + 2))) : Prop :=
  EG.card = n + 1 ∧ (SimpleGraph.fromRel (fun a b => (a, b) ∈ EG)).Connected

/-- §3.2, p. 216: a spanning tree `E^G` is an outtree rooted at `root` if every path in the tree
from `root` to another node `j` is directed from `root` to `j`; for a tree this says that every
node is reachable from `root` along arcs of `E^G`. -/
def IsSpanningOuttree (root : Fin (n + 2)) (EG : Finset (Fin (n + 2) × Fin (n + 2))) : Prop :=
  IsSpanningTree EG ∧ ∀ j, Relation.ReflTransGen (fun a b => (a, b) ∈ EG) root j

/-- Proposition 3.2.16 and Theorem 3.2.18 (pp. 217–218): `S` uniquely solves the system of
linear equations `S_0 = 0`, `S_j − S_i = w_ij` (`⟨i, j⟩ ∈ E^G`). -/
def UniquelySolves (w : Fin (n + 2) → Fin (n + 2) → ℤ) (EG : Finset (Fin (n + 2) × Fin (n + 2)))
    (S : Fin (n + 2) → ℝ) : Prop :=
  (S 0 = 0 ∧ ∀ e ∈ EG, S e.2 - S e.1 = (w e.1 e.2 : ℝ)) ∧
    ∀ T : Fin (n + 2) → ℝ, (T 0 = 0 ∧ ∀ e ∈ EG, T e.2 - T e.1 = (w e.1 e.2 : ℝ)) → T = S

/-- A directed walk in the project network `N` from `i` to `j` of length `w` (the sum of the arc
weights `δ` along the walk); the empty walk from `i` to `i` has length `0`. -/
inductive WalkLength (P : Project n K) : Fin (n + 2) → Fin (n + 2) → ℤ → Prop
  | refl (i : Fin (n + 2)) : WalkLength P i i 0
  | step {i j l : Fin (n + 2)} {w : ℤ} :
      WalkLength P i j w → (j, l) ∈ P.E → WalkLength P i l (w + P.δ j l)

end ProjSchedTW.StableSchedules


