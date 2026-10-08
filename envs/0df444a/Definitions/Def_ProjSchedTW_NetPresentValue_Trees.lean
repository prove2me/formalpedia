-- Prove2me | Definitions.Def_ProjSchedTW_NetPresentValue_Trees
-- name    : ProjSchedTW_NetPresentValue_Trees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:24:33.028591+00:00
-- url     : https://prove2.me/theorems/8c923f7c-b8ff-410b-b823-1076f73e3072
-- title:
--   §3.2 and §3.9.1 — spanning trees, forward and backward arcs, and subproject net present values
-- statement:
--   A set $E^G$ of arcs on $V$ is a **spanning tree** if it has $|V|-1=n+1$ arcs and its underlying undirected graph is connected. It is a **spanning outtree rooted at** $0$ if, in addition, every node is reached from $0$ along arcs of $E^G$ in their direction. A spanning tree $G=\langle V,E^G\rangle$ is **associated with** a schedule $S$ if $E^G\subseteq E$ and $S$ is the unique solution of
--   $$S_0=0,\qquad S_j-S_i=\delta_{ij}\quad(\langle i,j\rangle\in E^G).$$
--
--   For an arc $\langle i,j\rangle\in E^G$, let $V_{ij}$ be the node set of the subtree that results from $G$ by deleting $\langle i,j\rangle$ and that does not contain node $0$. The arc is a **forward arc** if the path in $G$ from $0$ passes it from $i$ to $j$ (so $j\in V_{ij}$), and a **backward arc** if it passes it from $j$ to $i$ (so $i\in V_{ij}$). The **net present value of the subproject** $V_{ij}$ is
--   $$npv^{ij}(S)=\sum_{h\in V_{ij}}c_h^F\beta^{S_h+p_h}.$$
--   The **sign conditions** at $S$ require $npv^{ij}(S)\ge0$ for every forward arc and $npv^{ij}(S)\le 0$ for every backward arc of $E^G$.
--
--   These objects state the optimality criterion of Proposition 3.9.2 for the net present value problem.
--
--   **Formalization Note** $V_{ij}$ is the set of nodes not connected to $0$ in the undirected graph of $E^G\setminus\{\langle i,j\rangle\}$. The book defines forward and backward arcs through a node sequence starting at $0$; in a tree this is the unique path from $0$, and the membership of the head or tail in $V_{ij}$ encodes it.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 216 (trees, outtrees, spanning trees), p. 217 (Proposition 3.2.16), p. 333 (forward and backward arcs, V_ij, npv^{ij}(S))

import Mathlib
import Definitions.Def_ProjSchedTW_NetPresentValue_Project
import Definitions.Def_ProjSchedTW_StableSchedules_Trees

namespace ProjSchedTW.NetPresentValue

variable {n : ℕ}

/-- Proposition 3.2.16 and §3.9.1 (pp. 217, 333): `E^G` is a spanning tree of the project network
`N` associated with schedule `S`: `E^G ⊆ E`, `E^G` is a spanning tree, and `S` uniquely solves
`S_0 = 0`, `S_j − S_i = δ_ij` (`⟨i, j⟩ ∈ E^G`), i.e. every tree arc is a binding temporal
constraint at `S` (tree weights `δ^G_ij = δ_ij`). -/
def IsAssociatedTree (P : Project n) (EG : Finset (Fin (n + 2) × Fin (n + 2)))
    (S : Fin (n + 2) → ℝ) : Prop :=
  EG ⊆ P.E ∧ ProjSchedTW.StableSchedules.IsSpanningTree EG ∧ ProjSchedTW.StableSchedules.UniquelySolves P.δ EG S

/-- §3.9.1 (p. 333): for an arc `e = ⟨i, j⟩` of the tree `E^G`, the node set `V_ij` of the subtree
that results from `G` by deleting arc `⟨i, j⟩` and that does not contain node `0`, i.e. the nodes
not connected to `0` in the underlying undirected graph of `E^G ∖ {⟨i, j⟩}`. -/
noncomputable def subtreeAway (EG : Finset (Fin (n + 2) × Fin (n + 2)))
    (e : Fin (n + 2) × Fin (n + 2)) : Finset (Fin (n + 2)) := by
  classical
  exact Finset.univ.filter
    (fun h => ¬ (SimpleGraph.fromRel (fun a b => (a, b) ∈ EG.erase e)).Reachable 0 h)

/-- §3.9.1 (p. 333): tree arc `⟨i, j⟩` is a forward arc in `G` if it is traversed from `i` to `j`
on the tree path starting at node `0`, i.e. if its head `j` lies in `V_ij` (away from `0`). -/
def IsForwardArc (EG : Finset (Fin (n + 2) × Fin (n + 2))) (e : Fin (n + 2) × Fin (n + 2)) :
    Prop :=
  e.2 ∈ subtreeAway EG e

/-- §3.9.1 (p. 333): tree arc `⟨i, j⟩` is a backward arc in `G` if it is traversed from `j` to `i`
on the tree path starting at node `0`, i.e. if its tail `i` lies in `V_ij` (away from `0`). -/
def IsBackwardArc (EG : Finset (Fin (n + 2) × Fin (n + 2))) (e : Fin (n + 2) × Fin (n + 2)) :
    Prop :=
  e.1 ∈ subtreeAway EG e

/-- §3.9.1 (p. 333): `npv^{ij}(S) = ∑_{h ∈ V_ij} c_h^F β^{S_h + p_h}`, the net present value of
the activities of `V_ij` given schedule `S`. -/
noncomputable def subtreeNPV (P : Project n) (β : ℝ) (c : Fin (n + 2) → ℝ)
    (EG : Finset (Fin (n + 2) × Fin (n + 2))) (e : Fin (n + 2) × Fin (n + 2))
    (S : Fin (n + 2) → ℝ) : ℝ :=
  ∑ h ∈ subtreeAway EG e, c h * β ^ (S h + (P.p h : ℝ))

/-- Proposition 3.9.2 (p. 333): the sign conditions on the spanning tree `E^G` at `S`:
`npv^{ij}(S) ≥ 0` for every forward arc and `npv^{ij}(S) ≤ 0` for every backward arc `⟨i, j⟩`. -/
def TreeSignCondition (P : Project n) (β : ℝ) (c : Fin (n + 2) → ℝ)
    (EG : Finset (Fin (n + 2) × Fin (n + 2))) (S : Fin (n + 2) → ℝ) : Prop :=
  ∀ e ∈ EG, (IsForwardArc EG e → 0 ≤ subtreeNPV P β c EG e S) ∧
    (IsBackwardArc EG e → subtreeNPV P β c EG e S ≤ 0)

end ProjSchedTW.NetPresentValue


