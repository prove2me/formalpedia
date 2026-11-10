-- Prove2me | Definitions.Def_SunMinCut_Cactus_CactusGraph
-- name    : SunMinCut_Cactus_CactusGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:22:48.745827+00:00
-- url     : https://prove2.me/theorems/2bbf6686-3ee9-4110-8598-6d3ab0298a3f
-- title:
--   Multigraph cactus and the cuts it represents
-- statement:
--   A multigraph $K$ has nodes $0,\dots,q-1$ and edges $0,\dots,e-1$, each with an unordered pair of ends (`MGraph`). A **cycle** is a nonempty edge set in which every node has degree $0$ or $2$ and whose touched nodes are connected through it (two parallel edges form a cycle of length two). $K$ is a **cactus** if it is connected, loopless, and every edge lies on at most one cycle; bridges and parallel two-cycles are allowed (App. G.2, p. 48). A **bridge** is an edge whose deletion disconnects $K$.
--
--   Given $\pi:V\to V(K)$ (not necessarily surjective: cactus nodes may be empty), the **represented shores** are $\pi^{-1}(X)$ where $X$ is the side containing one end of a bridge $b$ after deleting $b$, or the side containing one end of $e_1$ after deleting two distinct edges $e_1,e_2$ of one cycle. The represented cuts are the bipartitions $\{S,V\setminus S\}$ of represented shores. `(K, π)` **represents exactly all minimum cuts** of $G$ if $K$ is a cactus and the represented cuts equal the minimum cuts of $G$ (§1.1, p. 2: "The cactus represents each minimum cut by a bridge or two edges on one cycle"; App. G.2: "The represented family consists of bridge cuts and same-cycle two-edge cuts, lifted through π").
--
--   **Formalization Note** `SparseDisc.IsCactus` is not reused because it is `SimpleGraph`-only and cannot hold parallel two-cycles.
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, §1.1 p. 2, App. G.2 p. 48

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph

namespace SunMinCut.Cactus

/-- A finite multigraph with nodes `0, …, q-1` and edges `0, …, e-1` (no weights); used for
cacti, whose parallel two-cycles make a `SimpleGraph` unsuitable (App. G.2, p. 48). -/
structure MGraph (q e : ℕ) where
  /-- The unordered pair of ends of each edge. -/
  ends : Fin e → Sym2 (Fin q)

variable {q e : ℕ}

/-- The underlying adjacency of `K` after deleting the edge set `F`. -/
def MGraph.adjWithout (K : MGraph q e) (F : Finset (Fin e)) : SimpleGraph (Fin q) :=
  SimpleGraph.fromRel fun x y => ∃ i, i ∉ F ∧ K.ends i = s(x, y)

/-- The adjacency of `K` using only the edge set `C`. -/
def MGraph.adjOn (K : MGraph q e) (C : Finset (Fin e)) : SimpleGraph (Fin q) :=
  SimpleGraph.fromRel fun x y => ∃ i, i ∈ C ∧ K.ends i = s(x, y)

/-- `K` is connected. -/
def MGraph.Connected (K : MGraph q e) : Prop := (K.adjWithout ∅).Connected

/-- `K` has no loops. -/
def MGraph.Loopless (K : MGraph q e) : Prop := ∀ i, ¬ (K.ends i).IsDiag

open Classical in
/-- `C` is (the edge set of) a cycle of a loopless multigraph: a nonempty edge set in which every
node has degree `0` or `2` and whose touched nodes are connected through `C`. A pair of
parallel edges is a cycle of length two. -/
def MGraph.IsCycle (K : MGraph q e) (C : Finset (Fin e)) : Prop :=
  C.Nonempty ∧
  (∀ x, (C.filter fun i => x ∈ K.ends i).card = 0 ∨ (C.filter fun i => x ∈ K.ends i).card = 2) ∧
  ∀ x y, (∃ i ∈ C, x ∈ K.ends i) → (∃ j ∈ C, y ∈ K.ends j) → (K.adjOn C).Reachable x y

/-- A cactus (App. G.2, p. 48): a connected loopless multigraph in which every edge lies on at
most one cycle. Bridges and parallel two-cycles are allowed. -/
def MGraph.IsCactus (K : MGraph q e) : Prop :=
  K.Connected ∧ K.Loopless ∧
  ∀ i C C', K.IsCycle C → K.IsCycle C' → i ∈ C → i ∈ C' → C = C'

/-- The edge `i` is a bridge: deleting it disconnects `K`. -/
def MGraph.IsBridge (K : MGraph q e) (i : Fin e) : Prop := ¬ (K.adjWithout {i}).Connected

open Classical in
/-- The side containing `x` after deleting the edge set `F`. -/
noncomputable def MGraph.side (K : MGraph q e) (F : Finset (Fin e)) (x : Fin q) : Finset (Fin q) :=
  Finset.univ.filter fun y => (K.adjWithout F).Reachable x y

open Classical in
/-- The lift `π⁻¹(X)` of a set of cactus nodes to original vertices. -/
noncomputable def lift {n : ℕ} (π : Fin n → Fin q) (X : Finset (Fin q)) : Finset (Fin n) :=
  Finset.univ.filter fun v => π v ∈ X

/-- The shores represented by `(K, π)` (§1.1, p. 2; App. G.2, p. 48): the side of a bridge cut,
or of a two-edge cut by two distinct edges of the same cycle, lifted through `π`. -/
def repShores {n : ℕ} (K : MGraph q e) (π : Fin n → Fin q) : Set (Finset (Fin n)) :=
  {S | (∃ i, K.IsBridge i ∧ S = lift π (K.side {i} (Quot.out (K.ends i)).1)) ∨
       (∃ i j C, i ≠ j ∧ K.IsCycle C ∧ i ∈ C ∧ j ∈ C ∧
          S = lift π (K.side {i, j} (Quot.out (K.ends i)).1))}

/-- The cuts represented by `(K, π)`, as unordered bipartitions `{S, V ∖ S}`. -/
def repCuts {n : ℕ} (K : MGraph q e) (π : Fin n → Fin q) : Set (Finset (Finset (Fin n))) :=
  bip '' repShores K π

/-- `(K, π)` is a cactus representing exactly all minimum cuts of `G`: `K` is a cactus and the
family of represented bipartitions equals the family of minimum cuts. Cactus nodes may be empty
(`π` need not be surjective). -/
def RepresentsMinCuts {n m : ℕ} (G : Graph n m) (K : MGraph q e) (π : Fin n → Fin q) : Prop :=
  K.IsCactus ∧ repCuts K π = minCuts G

end SunMinCut.Cactus


