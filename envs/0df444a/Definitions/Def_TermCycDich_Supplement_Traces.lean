-- Prove2me | Definitions.Def_TermCycDich_Supplement_Traces
-- name    : TermCycDich_Supplement_Traces
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:46:04.837618+00:00
-- url     : https://prove2.me/theorems/cab01731-258d-4d24-b8b9-514da7b58f8d
-- title:
--   Grounded paths and cycles, traces, aligned discs, crops, $C$-discs and concentric cycles
-- statement:
--   Let $\rho$ be a $\Sigma$-rendition of a graph. A path or cycle $Q$ using no edge of a vortex is **grounded** if it is a path of length at least one with both ends in $\pi(N(\rho))$, or a cycle using edges of $\sigma(c_1)$ and $\sigma(c_2)$ for two distinct cells. Its **trace** is obtained as follows: every maximal piece of $Q$ inside one cell $c$ runs between two nodes $n_1,n_2$; take the component of $\mathrm{bd}(\bar c)-\{n_1,n_2\}$ selected by the tie-breaker (if $|N(c)|=2$) or avoiding $N(c)$ (if $|N(c)|=3$) and push it slightly off the cells; the union of these arcs is the trace, a closed curve for a cycle and an arc between nodes for a path.
--
--   A closed disc $\Delta\subseteq\Sigma$ is **$\rho$-aligned** if its boundary meets the painting only in nodes; the **crop** by $\Delta$ is the subgraph drawn onto $\Delta$. For a grounded cycle $C$ whose trace lies in a disc $\Delta$, the **$C$-disc** is the disc inside $\Delta$ bounded by the trace. Pairwise vertex-disjoint grounded cycles $C_1,\dots,C_s$ are **concentric** if their $C_i$-discs satisfy $\Delta_1\subsetneq\cdots\subsetneq\Delta_s$. For a subgraph $K$, a **$K$-path** is a $V(K)$-path of length at least one with no edge in $E(K)$. A subgraph is **grounded** if all its cycles are grounded and none of its vertices is drawn inside a vortex.
--
--   These notions describe how the solution and the concentric cycles of villages and railed annuli sit in the surface.
--
--   **Formalization Note** The trace is defined only up to the "slight push", so it is a relation: a pushed arc is an arc between the two nodes meeting cells and nodes only at its ends and bounding, together with the selected boundary arc, a disc whose interior meets no cell or node (the encoding of the public `GMSTFramework` traces). The arcs are taken between consecutive node vertices of the path. The crop by an annulus is the union of the $\sigma(c)$ of the cells inside it.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), §2.2 "Traces of paths and cycles" p.19 (PDF 21); "Aligned discs and grounded subgraphs", C-discs, concentric cycles p.20 (PDF 22); H-paths p.16 (PDF 18)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Graphs
import Definitions.Def_TermCycDich_Supplement_Rendition

open scoped Classical

noncomputable section

namespace TermCycDich

namespace Supplement

open GMSTFramework.LocalStructure

/-!
# Grounded paths and cycles, traces, aligned discs, crops, `C`-discs, concentric cycles

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held
version, sha256 34a10f1a…4d4ea1), §2.2 "Traces of paths and cycles" p.19 (PDF 21), "Aligned
discs and grounded subgraphs", `C`-discs, "Transactions and nests" (concentric cycles) p.20
(PDF 22); `H`-paths p.16 (PDF 18).

Paths are the public `GMSTFramework.LocalStructure.GPath` (a walk without repeated vertices; a
single vertex is a trivial path); cycles are subgraphs `C` with the public `IsCycleSub C`.

* `IsGroundedWalk`: the walk uses no edge of `σ(c)` for a vortex `c`, and either it is a path of
  length at least one with both ends in `π(N(ρ))`, or it is a cycle using edges of `σ(c₁)` and
  `σ(c₂)` for two distinct cells.
* **Traces** (p.19). Encoding (the same as the public `GMSTFramework` one, adapted to this
  rendition structure): for every pair of consecutive node vertices along the walk, the segment
  lies in one cell `c`; `L` is the component of `bd(c̄) − {n₁, n₂}` selected by the tie-breaker
  (`|N(c)| = 2`) or avoiding `N(c)` (`|N(c)| = 3`), and the pushed arc `L'` is an arc from `n₁` to
  `n₂` meeting the cells and nodes only in `n₁, n₂` such that `cl(L) ∪ L'` bounds a closed disc
  whose interior meets no cell and no node. A trace is the union of such arcs, pairwise meeting
  only in nodes. The paper defines the trace only up to this "slight push", so `IsTraceOfWalk` is
  a relation.
* `IsAlignedDisk Δ`: a closed disc whose boundary meets `U(Γ)` in nodes only. `crop ρ Δ`: the
  subgraph drawn onto `Δ` (nodes in `Δ` and the graphs of the cells inside `Δ`). `cropUnion ρ O`:
  the union of the `σ(c)` with `c ⊆ O` (the crop by an annulus, p.34).
* `IsCDiscIn ρ Δ C D T`: `C` is a grounded cycle, `T` is a trace of `C`, and `D ⊆ Δ` is the closed
  disc bounded by `T` ("if the trace is contained in a specified disc, we choose its `C`-disc
  inside that disc", p.20).
* `IsConcentricIn ρ Δ C D T`: `C₁, …, C_s` pairwise vertex-disjoint cycles of the crop by `Δ`,
  each grounded, with `Cᵢ`-discs `Dᵢ ⊆ Δ` and `D₁ ⊊ ⋯ ⊊ D_s` (indices `0`-based in Lean).
* `IsHPath K P`: a `V(K)`-path of length at least one with no edge in `E(K)` (p.16).
* `interiorOf D = D ∖ bd(D)` for a closed disc `D`.
-/

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {X : Type} [TopologicalSpace X]

/-- The open interior `D ∖ bd(D)` of a closed disc (or any subspace). -/
def interiorOf (D : Set X) : Set X := D \ manifoldBd D

/-- `P` is a `K`-path for the subgraph `K`: a `V(K)`-path of length at least one with no edge in
`E(K)`. -/
def IsHPath (K : G.Subgraph) (P : GPath G) : Prop :=
  IsAPath K.verts P ∧ 0 < P.walk.length ∧ ∀ e ∈ P.walk.edges, e ∉ K.edgeSet

namespace Rendition

variable {H : G.Subgraph} (ρ : Rendition X H)

/-- The walk is grounded: it uses no edge of a vortex, and either (`isPath`) it is a path of
length at least one with both ends nodes, or it uses edges of two distinct cells. -/
def IsGroundedWalk {u v : V} (w : G.Walk u v) (isPath : Prop) : Prop :=
  (∀ c ∈ ρ.vortices, ∀ e ∈ w.edges, e ∉ (ρ.σ c).edgeSet) ∧
    (if isPath then 0 < w.length ∧ u ∈ ρ.nodeVerts ∧ v ∈ ρ.nodeVerts
     else ∃ c₁ ∈ ρ.cells, ∃ c₂ ∈ ρ.cells, c₁ ≠ c₂ ∧ (∃ e ∈ w.edges, e ∈ (ρ.σ c₁).edgeSet) ∧
        ∃ e ∈ w.edges, e ∈ (ρ.σ c₂).edgeSet)

/-- A grounded path. -/
def GroundedPath (P : GPath G) : Prop := ρ.IsGroundedWalk P.walk True

/-- A grounded cycle (given as a subgraph). -/
def GroundedCycle (C : G.Subgraph) : Prop :=
  ∃ (u : V) (w : G.Walk u u), w.IsCycle ∧ w.toSubgraph = C ∧ ρ.IsGroundedWalk w False

/-- `L'` is a pushed boundary arc of the cell `c` between its nodes `a` and `b`. -/
def IsPushedArc (c : Set X) (a b : X) (L' : Set X) : Prop :=
  ∃ L : Set X,
    (∃ y ∈ manifoldBd (closure c) \ {a, b},
      L = connectedComponentIn (manifoldBd (closure c) \ {a, b}) y) ∧
    (if (ρ.nodesOf c).ncard = 2 then L = ρ.tie c else Disjoint L (ρ.nodesOf c)) ∧
    IsArc L' a b ∧ L' ∩ ((⋃ c' ∈ ρ.cells, c') ∪ ρ.N) ⊆ {a, b} ∧
    ∃ D : Set X, IsDiskWithBoundary D (closure L ∪ L') ∧
      (D \ (closure L ∪ L')) ∩ ((⋃ c' ∈ ρ.cells, c') ∪ ρ.N) = ∅

/-- The node-to-node segments of a walk: positions `i < j` whose vertices are nodes, with no node
strictly between. -/
def walkSegments {u v : V} (w : G.Walk u v) : Set (ℕ × ℕ) :=
  {ij | ij.1 < ij.2 ∧ ij.2 ≤ w.length ∧ w.getVert ij.1 ∈ ρ.nodeVerts ∧
    w.getVert ij.2 ∈ ρ.nodeVerts ∧ ∀ k, ij.1 < k → k < ij.2 → w.getVert k ∉ ρ.nodeVerts}

/-- `T` is a trace of the walk `w` in `ρ`: the union of one pushed boundary arc per node-to-node
segment (in the cell containing the segment's first edge), the arcs pairwise meeting only in
nodes. -/
def IsTraceOfWalk {u v : V} (w : G.Walk u v) (T : Set X) : Prop :=
  ∃ L : ℕ × ℕ → Set X, T = (⋃ ij ∈ ρ.walkSegments w, L ij) ∧
    (∀ ij ∈ ρ.walkSegments w, ∃ a ∈ ρ.N, ∃ b ∈ ρ.N,
      ρ.π a = w.getVert ij.1 ∧ ρ.π b = w.getVert ij.2 ∧
      ∃ c ∈ ρ.cells, s(w.getVert ij.1, w.getVert (ij.1 + 1)) ∈ (ρ.σ c).edgeSet ∧
        ρ.IsPushedArc c a b (L ij)) ∧
    ∀ ij ∈ ρ.walkSegments w, ∀ ij' ∈ ρ.walkSegments w, ij ≠ ij' → L ij ∩ L ij' ⊆ ρ.N

/-- `T` is a trace of the grounded path `P`. -/
def IsTracePath (P : GPath G) (T : Set X) : Prop := ρ.GroundedPath P ∧ ρ.IsTraceOfWalk P.walk T

/-- `T` is a trace of the grounded cycle `C` (computed from a closed walk around `C` starting at a
node). -/
def IsTraceCycle (C : G.Subgraph) (T : Set X) : Prop :=
  ρ.GroundedCycle C ∧
    ∃ u ∈ ρ.nodeVerts, ∃ w : G.Walk u u, w.IsCycle ∧ w.toSubgraph = C ∧ ρ.IsTraceOfWalk w T

/-- A `ρ`-aligned disc: a closed disc whose boundary meets `U(Γ)` in nodes only. -/
def IsAlignedDisk (Δ : Set X) : Prop :=
  ∃ T : Set X, IsDiskWithBoundary Δ T ∧ T ∩ ρ.U ⊆ ρ.N

/-- The crop by the set `Δ`: the nodes in `Δ` and the graphs of the cells inside `Δ`. -/
def crop (Δ : Set X) : G.Subgraph :=
  isolatedSub (ρ.π '' (ρ.N ∩ Δ)) ⊔ ⨆ c ∈ {c | c ∈ ρ.cells ∧ c ⊆ Δ}, ρ.σ c

/-- The union of the graphs `σ(c)` of the cells `c ⊆ O` (the crop by an annulus, p.34). -/
def cropUnion (O : Set X) : G.Subgraph := ⨆ c ∈ {c | c ∈ ρ.cells ∧ c ⊆ O}, ρ.σ c

/-- `D` is the `C`-disc inside the disc `Δ`, bounded by the trace `T` of the grounded cycle `C`. -/
def IsCDiscIn (Δ : Set X) (C : G.Subgraph) (D T : Set X) : Prop :=
  ρ.IsTraceCycle C T ∧ IsDiskWithBoundary D T ∧ D ⊆ Δ

/-- `C₀, …, C_{s-1}` are concentric cycles in the restriction of `ρ` to the disc `Δ`, with
`Cᵢ`-discs `Dᵢ` bounded by traces `Tᵢ`: pairwise vertex-disjoint cycles of the crop by `Δ`, each
grounded, with `D₀ ⊊ D₁ ⊊ ⋯ ⊊ D_{s-1} ⊆ Δ`. -/
def IsConcentricIn (Δ : Set X) {s : ℕ} (C : Fin s → G.Subgraph) (D T : Fin s → Set X) : Prop :=
  (∀ i, IsCycleSub (C i) ∧ C i ≤ ρ.crop Δ) ∧
    Pairwise (fun i j => Disjoint (C i).verts (C j).verts) ∧
    (∀ i, ρ.IsCDiscIn Δ (C i) (D i) (T i)) ∧
    ∀ i j, i < j → D i ⊂ D j

/-- The subgraph `K` is grounded: every cycle of `K` is grounded and no vertex of `K` is drawn
inside a vortex (in `σ(c)` for a vortex `c` without being a node of `c`). -/
def GroundedSub (K : G.Subgraph) : Prop :=
  (∀ C : G.Subgraph, IsCycleSub C → C ≤ K → ρ.GroundedCycle C) ∧
    ∀ v ∈ K.verts, ∀ c ∈ ρ.vortices, v ∈ (ρ.σ c).verts → v ∈ ρ.cellNodeVerts c

end Rendition

end Supplement

end TermCycDich


