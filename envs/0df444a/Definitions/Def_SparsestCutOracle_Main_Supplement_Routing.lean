-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Supplement_Routing
-- name    : SparsestCutOracle_Main_Supplement_Routing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:46:22.888318+00:00
-- url     : https://prove2.me/theorems/53be6d2f-41be-4e9b-a4cf-dbc3f3408c19
-- title:
--   Partitions, boundary degrees and induced demand routing
-- statement:
--   Let $G$ be a finite undirected graph represented by an oriented edge list on $V=\{0,\ldots,n-1\}$, with a nonnegative real capacity $c_e$ on each edge, including separate entries for parallel edges. A partition of $U\subseteq V$ is a finite family of nonempty, pairwise disjoint blocks whose union is $U$. Its boundary is the union of the boundaries of its blocks, counting each listed edge once. The boundary degree of a vertex sums the capacities of its incident boundary edges; edges leaving $U$ are included.
--
--   A signed demand on $X\subseteq V$ vanishes off $X$ and sums to zero on $X$. An edge flow assigns a signed real number to each oriented edge. Its aggregate vertex-pair flow is antisymmetric, and positive divergence means net outflow. Routing with a congestion vector $\operatorname{con}$ inside $G[X]$ means
--   $$
--   \operatorname{div} f=d,\qquad |f_e|\le\operatorname{con}_e c_e,\qquad f_e=0\ \text{if }e\notin G[X].
--   $$
--   Zero-capacity edges carry zero flow. This extends the published flow layer to arbitrary congestion and induced subgraphs without changing its divergence convention.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 8, 44–45, §2 and §8.2.1–8.2.2

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_FairFlow

namespace SparsestCutOracle.Main.Supplement

abbrev VertexSet (n : ℕ) := Finset (Fin n)
abbrev Partition (n : ℕ) := Finset (VertexSet n)

/-- A partition of U; empty blocks are forbidden, including for proper subsets U. -/
def IsPartition {n : ℕ} (U : VertexSet n) (P : Partition n) : Prop :=
  (∀ X ∈ P, X.Nonempty) ∧
  (∀ X ∈ P, ∀ Y ∈ P, X ≠ Y → Disjoint X Y) ∧
  P.biUnion id = U

/-- An edge is counted once in a partition boundary, even if it borders two blocks. -/
def OnBoundary {n : ℕ} (P : Partition n) (e : Edge n) : Prop :=
  ∃ X ∈ P, (e.u ∈ X ∧ e.v ∉ X) ∨ (e.v ∈ X ∧ e.u ∉ X)

noncomputable def boundaryDegree {n : ℕ} (G : Graph n) (P : Partition n)
    (v : Fin n) : ℝ := by
  classical
  exact ∑ j : Fin G.length,
    if OnBoundary P G[j.val] ∧ (G[j.val].u = v ∨ G[j.val].v = v)
    then (G[j.val].capacity : ℝ) else 0

/-- Signed edge flows retain individual bounds for parallel edges. Their aggregate is
an antisymmetric Flow with the published netFlow convention (positive = outflow). -/
def edgeFlow {n : ℕ} (G : Graph n) (f : Fin G.length → ℝ) : Flow n :=
  fun u v => ∑ j : Fin G.length,
    ((if G[j.val].u = u ∧ G[j.val].v = v then f j else 0) -
      (if G[j.val].v = u ∧ G[j.val].u = v then f j else 0))

def DemandOn {n : ℕ} (X : VertexSet n) (d : Fin n → ℝ) : Prop :=
  (∀ v, v ∉ X → d v = 0) ∧ mass d X = 0

/-- Induced routing, with a separate congestion bound on each listed edge.
A zero capacity forces zero flow; an edge outside G[X] carries zero flow. -/
def RoutesOn {n : ℕ} (G : Graph n) (X : VertexSet n) (d : Fin n → ℝ)
    (con : Fin G.length → ℝ) : Prop :=
  ∃ f : Fin G.length → ℝ,
    (∀ j, G[j.val].u ∉ X ∨ G[j.val].v ∉ X → f j = 0) ∧
    (∀ j, |f j| ≤ con j * (G[j.val].capacity : ℝ)) ∧
    (∀ u v, edgeFlow G f u v = -edgeFlow G f v u) ∧
    (∀ v, netFlow (edgeFlow G f) v = d v)

end SparsestCutOracle.Main.Supplement


