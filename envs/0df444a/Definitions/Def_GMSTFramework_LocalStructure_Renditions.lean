-- Prove2me | Definitions.Def_GMSTFramework_LocalStructure_Renditions
-- name    : GMSTFramework_LocalStructure_Renditions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:01:03.158087+00:00
-- url     : https://prove2.me/theorems/47f2c56c-24eb-4bb8-bad2-dfe48d152352
-- title:
--   Paintings, $\Sigma$-renditions (floating-cell convention, tie-breakers), traces, grounded and flat subgraphs, aligned disks, crops, inner/outer graphs, major apices, flat meshes (§2.3.2, §5.1)
-- statement:
--   A **painting** in $\Sigma$ is $\Gamma=(U,N)$ with $N\subseteq U\subseteq\Sigma$, $N$ finite, finitely many arc-components (**cells**) of $U\setminus N$, each cell closure $\bar c$ a closed disk with $N(c)=\bar c\cap N\subseteq\mathrm{bd}(\bar c)$, and distinct cell closures meeting only in $N$. A cell is floating ($|N(c)|=0$), simple ($|N(c)|\in[3]$) or a vortex ($|N(c)|\ge4$). A **$\Sigma$-rendition** of $G$ is $\rho=(\Gamma,\sigma,\pi)$ with $\sigma(c)\subseteq G$ and $\pi:N\to V(G)$ injective satisfying R1 $G=(\pi(N),\emptyset)\cup\bigcup_c\sigma(c)$; R2 distinct cells have edge-disjoint graphs; R3 $\pi(N(c))\subseteq V(\sigma(c))$; R4 $V(\sigma(c))\cap(\pi(N)\cup\bigcup_{c'\ne c}V(\sigma(c')))\subseteq\pi(N(c))$. Convention: there is a unique floating cell and it carries every component of $G$ without a node. Every rendition carries a tie-breaker: for each cell with two nodes a chosen component of $\mathrm{bd}(\bar c)-N(c)$.
--
--   A path or cycle is **grounded** if it uses no vortex edge and uses edges of two distinct cells (or is a path with both ends nodes). Its **trace** is the union of the boundary arcs $L_i$ (selected by the tie-breaker, or avoiding $N(c)$ when $|N(c)|=3$) between consecutive nodes along it, pushed slightly off the cells. A disk is **$\rho$-aligned** if its boundary meets $\Gamma$ only in nodes; the **$C$-disk** of a grounded cycle $C$ is an aligned disk bounded by its trace; the **crop** by $\Delta$ is the graph drawn in $\Delta$; the inner graph of $C$ is the crop by its disk plus $C$, the outer graph is $G[B\cup(V(G)\setminus V(G'))]\cup C$ with $B=\pi(N\cap\mathrm{bd}\,\Delta_C)$. A (2-connected) subgraph is **grounded** if all its cycles are grounded and none of its vertices is drawn in a vortex; a planar subgraph is **flat** if moreover an aligned disk without vortices contains every cell sharing an edge with it. $v\in A$ is a **major apex** if there is a non-vortex cell and $v$ has a neighbour outside $A$ and outside all vortex graphs. $M$ is a **flat mesh** in $G$ if some sphere-rendition of $G$ with a single vortex $c_0$ has $M$ flat and the trace of the perimeter of $M$ separates every node of $M$ from $c_0$.
--
--   **Formalization Note.** A rendition is of a subgraph `H` of the ambient graph (`G - A` is `minusVerts G A`). Traces are relations: `IsPushedArc` says that $L'$ is an arc between the two nodes meeting cells and nodes only in its ends and bounding, together with $L$, a closed disk whose interior meets no cell and no node; `IsTraceOfWalk` takes one such arc per node-to-node segment, pairwise meeting only in nodes; a cycle's trace is computed from a closed walk starting at a node. Every property the paper uses (bounding a disk, contractibility, avoiding, separating) is invariant under the push, so "the trace" is read as "a trace" in hypotheses and "every trace" where the paper asserts a property of it. The major-apex definition keeps the printed "there exists a non-vortex cell $c$" (always true, by the floating cell). "Separates every node of $M$ from $c_0$": no such node lies in the component of $\Sigma\setminus T$ containing a point of $c_0$.
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), p. 14–17, 19 (PDF 17–20, 22), §2.3.2, "Inner and outer graphs"; p. 39 (PDF 42) "Flat meshes"

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Surfaces
import Definitions.Def_GMSTFramework_LocalStructure_Graphs

open scoped Classical

noncomputable section

namespace GMSTFramework.LocalStructure

/-!
# Paintings, `Σ`-renditions, traces, grounded and flat subgraphs, apices, flat meshes

Gorsky, Protopapas, Wiederrecht, *A unifying framework for Graph Minor Structure Theorems with
polynomial bounds*, STOC 2027 submission (manuscript sha256 b2ee466d…), §2.3.2 p. 14–17
(PDF 17–20), §2.3.3 "Inner and outer graphs" p. 19 (PDF 22), §5.1 "Flat meshes" p. 39 (PDF 42).

* `cellsOf U N`: the arcwise-connected (path-connected) components of `U \ N`.
* `Painting X`: `N ⊆ U ⊆ X`, `N` finite, finitely many cells, every cell closure `c̄` a closed
  disk with `c̄ ∩ N ⊆ bd(c̄)`, distinct cell closures meeting only in `N`.
  `nodesOf c = c̄ ∩ N`; a cell is floating (`|N(c)| = 0`), simple (`|N(c)| ∈ [3]`) or a vortex
  (`|N(c)| ≥ 4`).
* `Rendition X H`: a `X`-rendition `ρ = (Γ, σ, π)` of the graph `H` (a subgraph of the ambient
  graph `G`, e.g. `G - A`): `σ(c) ≤ H` for every cell, `π` injective on `N`, R1–R4 (p. 14), the
  **floating-cell convention** of p. 15 (exactly one floating cell, and it carries every component
  of `H` that contains no node), and a **tie-breaker** (p. 16): for every cell with exactly two
  nodes, a selected component of `bd(c̄) − N(c)`.
* Grounded paths and cycles (p. 16): no edge in a vortex, and edges in two distinct cells (or, for
  a path, both ends nodes).
* **Traces** (p. 16). The paper pushes the boundary arcs `Lᵢ` "slightly" off the cells. Encoding:
  `IsPushedArc ρ c a b L'` says that `L'` is an arc from node `a` to node `b` meeting the cells and
  nodes only in `a, b`, such that `L'` together with the boundary arc `L` of `c̄` selected by the
  paper's rule (the tie-breaker component when `|N(c)| = 2`, the component avoiding `N(c)` when
  `|N(c)| = 3`) bounds a closed disk whose interior meets no cell and no node. `IsTraceOfWalk`
  takes one such arc for every pair of consecutive nodes along the walk (the maximal subpaths inside
  one cell and internally disjoint from `N(ρ)`), pairwise meeting only in nodes; a trace of a cycle
  is computed from a closed walk starting at a node. Every property used below (bounding a disk,
  being contractible, avoiding another set, separating) is the paper's and is invariant under the
  choice of push; a trace is therefore a relation, not a function. End pieces of a path whose end is
  not a node lie in no node-to-node segment and contribute nothing (the paper's definition only
  covers node-to-node pieces).
* `ρ`-aligned disks, `C`-disks (a disk bounded by a trace of the grounded cycle `C`), crops, inner
  and outer graphs of a cycle, grounded and flat subgraphs, major apices.
* `WitnessesFlatMesh ρ M`, `IsFlatMesh H M` (p. 39): some sphere-rendition of `H` with a single
  vortex `c₀` in which `M` is flat and the trace of the perimeter of `M` separates every node of
  `M` from `c₀` (no such node lies in the component of `Σ − trace` containing a point of `c₀`).
-/

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {X : Type} [TopologicalSpace X]

/-- The cells of a painting: the path components of `U \ N`. -/
def cellsOf (U N : Set X) : Set (Set X) :=
  {c | ∃ x ∈ U \ N, c = pathComponentIn (U \ N) x}

/-- A painting `Γ = (U, N)` in `X`. -/
structure Painting (X : Type) [TopologicalSpace X] where
  /-- the drawn set -/
  U : Set X
  /-- the nodes -/
  N : Set X
  N_sub : N ⊆ U
  N_finite : N.Finite
  cells_finite : (cellsOf U N).Finite
  closure_disk : ∀ c ∈ cellsOf U N, IsClosedDisk (closure c) ∧ closure c ∩ N ⊆ manifoldBd (closure c)
  closure_meet : ∀ c ∈ cellsOf U N, ∀ c' ∈ cellsOf U N, c ≠ c' → closure c ∩ closure c' ⊆ N

namespace Painting

/-- The cells `C(Γ)`. -/
def cells (Γ : Painting X) : Set (Set X) := cellsOf Γ.U Γ.N

/-- `N_Γ(c) = c̄ ∩ N`. -/
def nodesOf (Γ : Painting X) (c : Set X) : Set X := closure c ∩ Γ.N

/-- Simple cell: `|N(c)| ∈ [3]`. -/
def IsSimple (Γ : Painting X) (c : Set X) : Prop :=
  c ∈ Γ.cells ∧ 1 ≤ (Γ.nodesOf c).ncard ∧ (Γ.nodesOf c).ncard ≤ 3

/-- Vortex: `|N(c)| ≥ 4`. -/
def IsVortex (Γ : Painting X) (c : Set X) : Prop := c ∈ Γ.cells ∧ 4 ≤ (Γ.nodesOf c).ncard

/-- Floating cell: `N(c) = ∅`. -/
def IsFloating (Γ : Painting X) (c : Set X) : Prop := c ∈ Γ.cells ∧ Γ.nodesOf c = ∅

/-- The vortex cells. -/
def vortices (Γ : Painting X) : Set (Set X) := {c | Γ.IsVortex c}

end Painting

/-- The subgraph with vertex set `S` and no edges. -/
def isolatedSub (S : Set V) : G.Subgraph where
  verts := S
  Adj := fun _ _ => False
  adj_sub := fun h => h.elim
  edge_vert := fun h => h.elim
  symm := ⟨fun _ _ h => h⟩

/-- A `X`-rendition `ρ = (Γ, σ, π)` of the graph `H ≤ G`, with the floating-cell convention and a
tie-breaker. -/
structure Rendition (X : Type) [TopologicalSpace X] (H : G.Subgraph) extends Painting X where
  /-- the graph drawn in each cell -/
  σ : Set X → G.Subgraph
  /-- the vertex of each node -/
  π : X → V
  π_inj : Set.InjOn π N
  σ_le : ∀ c ∈ cellsOf U N, σ c ≤ H
  R1_verts : H.verts = π '' N ∪ ⋃ c ∈ cellsOf U N, (σ c).verts
  R1_edges : H.edgeSet = ⋃ c ∈ cellsOf U N, (σ c).edgeSet
  R2 : ∀ c ∈ cellsOf U N, ∀ c' ∈ cellsOf U N, c ≠ c' → Disjoint (σ c).edgeSet (σ c').edgeSet
  R3 : ∀ c ∈ cellsOf U N, π '' (closure c ∩ N) ⊆ (σ c).verts
  R4 : ∀ c ∈ cellsOf U N,
    (σ c).verts ∩ (π '' N ∪ ⋃ c' ∈ cellsOf U N \ {c}, (σ c').verts) ⊆ π '' (closure c ∩ N)
  /-- convention: a unique floating cell -/
  floating_unique : ∃! c, c ∈ cellsOf U N ∧ closure c ∩ N = ∅
  /-- convention: the floating cell carries every component of `H` without a node -/
  floating_carries : ∀ c ∈ cellsOf U N, closure c ∩ N = ∅ →
    ∀ v ∈ H.verts, (∀ x ∈ N, ¬ H.spanningCoe.Reachable v (π x)) →
      v ∈ (σ c).verts ∧ ∀ w, H.Adj v w → (σ c).Adj v w
  /-- the tie-breaker -/
  tie : Set X → Set X
  tie_spec : ∀ c ∈ cellsOf U N, (closure c ∩ N).ncard = 2 →
    ∃ y ∈ manifoldBd (closure c) \ (closure c ∩ N),
      tie c = connectedComponentIn (manifoldBd (closure c) \ (closure c ∩ N)) y

namespace Rendition

variable {H : G.Subgraph} (ρ : Rendition X H)

/-- The vertices of `G` that are nodes, `π(N(ρ))`. -/
def nodeVerts : Set V := ρ.π '' ρ.N

/-- The vertices `π(N(c))` of the nodes of a cell. -/
def cellNodeVerts (c : Set X) : Set V := ρ.π '' ρ.nodesOf c

/-- The number of vortices (the breadth of `ρ`). -/
def breadth : ℕ := ρ.vortices.ncard

/-- A walk is grounded: it uses no edge of a vortex, and either uses edges of two distinct cells or
(`isPath`) is a path with both ends nodes. -/
def IsGroundedWalk {u v : V} (w : G.Walk u v) (isPath : Prop) : Prop :=
  (∀ c ∈ ρ.vortices, ∀ e ∈ w.edges, e ∉ (ρ.σ c).edgeSet) ∧
    ((∃ c₁ ∈ ρ.cells, ∃ c₂ ∈ ρ.cells, c₁ ≠ c₂ ∧ (∃ e ∈ w.edges, e ∈ (ρ.σ c₁).edgeSet) ∧
        ∃ e ∈ w.edges, e ∈ (ρ.σ c₂).edgeSet) ∨
      (isPath ∧ u ∈ ρ.nodeVerts ∧ v ∈ ρ.nodeVerts))

/-- A grounded path. -/
def GroundedPath (P : GPath G) : Prop := ρ.IsGroundedWalk P.walk True

/-- A grounded cycle (given as a subgraph). -/
def GroundedCycle (C : G.Subgraph) : Prop :=
  ∃ (u : V) (w : G.Walk u u), w.IsCycle ∧ w.toSubgraph = C ∧ ρ.IsGroundedWalk w False

/-- `L'` is a pushed boundary arc of the cell `c` between its nodes `a` and `b` (see the module
docstring). -/
def IsPushedArc (c : Set X) (a b : X) (L' : Set X) : Prop :=
  ∃ L : Set X,
    (∃ y ∈ manifoldBd (closure c) \ {a, b},
      L = connectedComponentIn (manifoldBd (closure c) \ {a, b}) y) ∧
    (if (ρ.nodesOf c).ncard = 2 then L = ρ.tie c else Disjoint L (ρ.nodesOf c)) ∧
    IsArc L' a b ∧ L' ∩ ((⋃ c' ∈ ρ.cells, c') ∪ ρ.N) ⊆ {a, b} ∧
    ∃ D : Set X, IsDiskWithBoundary D (closure L ∪ L') ∧
      (D \ (closure L ∪ L')) ∩ ((⋃ c' ∈ ρ.cells, c') ∪ ρ.N) = ∅

/-- The node-to-node segments of a walk: pairs of positions `i < j` whose vertices are nodes, with
no node strictly between. -/
def walkSegments {u v : V} (w : G.Walk u v) : Set (ℕ × ℕ) :=
  {ij | ij.1 < ij.2 ∧ ij.2 ≤ w.length ∧ w.getVert ij.1 ∈ ρ.nodeVerts ∧
    w.getVert ij.2 ∈ ρ.nodeVerts ∧ ∀ k, ij.1 < k → k < ij.2 → w.getVert k ∉ ρ.nodeVerts}

/-- `T` is a trace of the walk `w` in `ρ`: the union of one pushed boundary arc per node-to-node
segment (in the cell containing the segment's edges), the arcs pairwise meeting only in nodes. -/
def IsTraceOfWalk {u v : V} (w : G.Walk u v) (T : Set X) : Prop :=
  ∃ L : ℕ × ℕ → Set X, T = (⋃ ij ∈ ρ.walkSegments w, L ij) ∧
    (∀ ij ∈ ρ.walkSegments w, ∃ a ∈ ρ.N, ∃ b ∈ ρ.N,
      ρ.π a = w.getVert ij.1 ∧ ρ.π b = w.getVert ij.2 ∧
      ∃ c ∈ ρ.cells, s(w.getVert ij.1, w.getVert (ij.1 + 1)) ∈ (ρ.σ c).edgeSet ∧
        ρ.IsPushedArc c a b (L ij)) ∧
    ∀ ij ∈ ρ.walkSegments w, ∀ ij' ∈ ρ.walkSegments w, ij ≠ ij' → L ij ∩ L ij' ⊆ ρ.N

/-- `T` is a trace of the path `P`. -/
def IsTracePath (P : GPath G) (T : Set X) : Prop := ρ.IsTraceOfWalk P.walk T

/-- `T` is a trace of the cycle `C` (computed from a closed walk around `C` starting at a node). -/
def IsTraceCycle (C : G.Subgraph) (T : Set X) : Prop :=
  ∃ u ∈ ρ.nodeVerts, ∃ w : G.Walk u u, w.IsCycle ∧ w.toSubgraph = C ∧ ρ.IsTraceOfWalk w T

/-- A `ρ`-aligned disk: a closed disk whose boundary meets `Γ` only in nodes. -/
def IsAlignedDisk (Δ : Set X) : Prop :=
  ∃ T : Set X, IsDiskWithBoundary Δ T ∧ T ∩ ρ.U ⊆ ρ.N

/-- `Δ` is a `C`-disk with boundary `T`: `C` is grounded, `T` is a trace of `C`, and `Δ` is a
`ρ`-aligned closed disk bounded by `T`. -/
def IsCDiskWith (C : G.Subgraph) (Δ T : Set X) : Prop :=
  ρ.GroundedCycle C ∧ ρ.IsTraceCycle C T ∧ IsDiskWithBoundary Δ T ∧ T ∩ ρ.U ⊆ ρ.N

/-- `Δ` is a `C`-disk. -/
def IsCDisk (C : G.Subgraph) (Δ : Set X) : Prop := ∃ T, ρ.IsCDiskWith C Δ T

/-- The crop of `H` by the disk `Δ`: the nodes in `Δ` and the graphs of the cells inside `Δ`. -/
def crop (Δ : Set X) : G.Subgraph :=
  isolatedSub (ρ.π '' (ρ.N ∩ Δ)) ⊔ ⨆ c ∈ {c | c ∈ ρ.cells ∧ c ⊆ Δ}, ρ.σ c

/-- The inner graph `G' ∪ C` of the cycle `C` with respect to the `C`-disk `Δ`. -/
def innerGraph (Δ : Set X) (C : G.Subgraph) : G.Subgraph := ρ.crop Δ ⊔ C

/-- The outer graph `H[B ∪ (V(H) \ V(G'))] ∪ C` of the cycle `C` with respect to the `C`-disk `Δ`
with boundary `T`, where `G'` is the crop by `Δ` and `B = π(N(ρ) ∩ T)`. -/
def outerGraph (Δ T : Set X) (C : G.Subgraph) : G.Subgraph :=
  H.induce (ρ.π '' (ρ.N ∩ T) ∪ (H.verts \ (ρ.crop Δ).verts)) ⊔ C

/-- A subgraph is grounded: every cycle of it is grounded and none of its vertices is drawn inside
a vortex (in `σ(c)` for a vortex `c` without being a node of `c`). -/
def GroundedSub (S : G.Subgraph) : Prop :=
  (∀ C : G.Subgraph, IsCycleSub C → C ≤ S → ρ.GroundedCycle C) ∧
    ∀ v ∈ S.verts, ∀ c ∈ ρ.vortices, v ∈ (ρ.σ c).verts → v ∈ ρ.cellNodeVerts c

/-- A (planar) subgraph is flat in `ρ`: grounded, and some `ρ`-aligned disk contains every cell
whose graph shares an edge with it and contains no vortex. -/
def FlatSub (S : G.Subgraph) : Prop :=
  ρ.GroundedSub S ∧ ∃ Δ : Set X, ρ.IsAlignedDisk Δ ∧
    (∀ c ∈ ρ.cells, ((ρ.σ c).edgeSet ∩ S.edgeSet).Nonempty → c ⊆ Δ) ∧
    ∀ c ∈ ρ.vortices, ¬ c ⊆ Δ

end Rendition

/-- `v ∈ A` is a major apex with respect to the rendition `ρ` of `G - A`: there is a non-vortex cell
`c` (as printed) and `v` has a neighbour outside `A` and outside every vortex graph. -/
def IsMajorApex (A : Finset V) {H : G.Subgraph} (ρ : Rendition X H) (v : V) : Prop :=
  v ∈ A ∧ (∃ c ∈ ρ.cells, ¬ ρ.IsVortex c) ∧
    ∃ w, G.Adj v w ∧ w ∉ A ∧ ∀ c ∈ ρ.vortices, w ∉ (ρ.σ c).verts

/-- The major apices `A^major ⊆ A`. -/
def majorApices (A : Finset V) {H : G.Subgraph} (ρ : Rendition X H) : Finset V :=
  A.filter fun v => IsMajorApex A ρ v

/-- `G - Z` as a subgraph of `G`. -/
def minusVerts (G : SimpleGraph V) (Z : Set V) : G.Subgraph := (⊤ : G.Subgraph).deleteVerts Z

/-- The sphere-rendition `ρ` of `H` witnesses that the mesh `M ≤ H` is flat: `ρ` has a single
vortex `c₀`, `M` is flat in `ρ`, and some trace of the perimeter of `M` separates every node of `M`
from `c₀`. -/
def WitnessesFlatMesh {H : G.Subgraph} {n m : ℕ} (ρ : Rendition TheSphere H) (M : Mesh G n m) :
    Prop :=
  M.sub ≤ H ∧ ρ.vortices.ncard = 1 ∧ ρ.FlatSub M.sub ∧
    ∃ T, ρ.IsTraceCycle M.perimeter T ∧
      ∀ c₀ ∈ ρ.vortices, ∀ y ∈ c₀, ∀ x ∈ ρ.N, ρ.π x ∈ M.verts → x ∉ connectedComponentIn Tᶜ y

/-- `M` is a flat mesh in `H`. -/
def IsFlatMesh (H : G.Subgraph) {n m : ℕ} (M : Mesh G n m) : Prop :=
  ∃ ρ : Rendition TheSphere H, WitnessesFlatMesh ρ M

end GMSTFramework.LocalStructure


