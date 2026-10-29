-- Prove2me | Definitions.Def_FairDivisionGraph_TreeMMS_Model
-- name    : FairDivisionGraph_TreeMMS_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:06.478387+00:00
-- url     : https://prove2.me/theorems/4bf16a8c-2bb8-419c-a07f-1e511dff1752
-- title:
--   Connected fair division: utilities, allocations and connected partitions
-- statement:
--   There are $m$ indivisible vertices and $n$ agents, labelled from zero. Each utility table entry is real. Bundle value is the sum of its item values. An initial CFD instance has $1\le n\le m$, nonnegative utilities and total utility one for every agent.
--
--   An allocation assigns a vertex subset to each agent. It is valid when bundles are pairwise disjoint and each is empty or induces a connected subgraph. Completeness, defined separately, means that every vertex is assigned. A connected $k$-partition of a residual vertex set $V$ consists of $k$ nonempty, pairwise disjoint, induced-connected subsets whose union is exactly $V$.
--
--   These definitions use finite simple undirected graphs. Raw bundle values and partitions do not assume normalization, so they also describe restricted recursive instances.
-- source:
--   Bouveret, Cechlárová, Elkind, Igarashi and Peters (2017), Fair Division of a Graph, IJCAI-17, https://doi.org/10.24963/ijcai.2017/20, Definition 2.1 and §2, printed p. 136 (PDF p. 2)

import Mathlib

set_option autoImplicit false

namespace FairDivisionGraph.TreeMMS

/-- Additive value; no normalization is built into this raw operation. -/
def value {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) : ℝ := ∑ v ∈ S, u v

/-- Initial CFD utility assumptions, including the standing cardinality convention. -/
def IsCFD {m n : ℕ} (u : Fin n → Fin m → ℝ) : Prop :=
  0 < n ∧ n ≤ m ∧ (∀ i v, 0 ≤ u i v) ∧ (∀ i, value (u i) Finset.univ = 1)

/-- Empty bundles are permitted; every nonempty bundle induces a connected graph. -/
def BundleConnected {m : ℕ} (G : SimpleGraph (Fin m)) (S : Finset (Fin m)) : Prop :=
  S = ∅ ∨ (G.induce (S : Set (Fin m))).Connected

/-- General valid allocations need not cover all vertices. -/
def Valid {m n : ℕ} (G : SimpleGraph (Fin m)) (π : Fin n → Finset (Fin m)) : Prop :=
  (∀ i, BundleConnected G (π i)) ∧ (∀ i j, i ≠ j → Disjoint (π i) (π j))

/-- Completeness is separate from validity. -/
def Complete {m n : ℕ} (π : Fin n → Finset (Fin m)) : Prop :=
  ∀ v, ∃ i, v ∈ π i

/-- A labelled partition of a residual vertex set into nonempty connected parts. -/
def ConnectedPartition {m k : ℕ} (G : SimpleGraph (Fin m))
    (V : Finset (Fin m)) (P : Fin k → Finset (Fin m)) : Prop :=
  (∀ j, P j ⊆ V ∧ (P j).Nonempty ∧ (G.induce (P j : Set (Fin m))).Connected) ∧
  (∀ j l, j ≠ l → Disjoint (P j) (P l)) ∧
  (∀ v, v ∈ V ↔ ∃ j, v ∈ P j)

end FairDivisionGraph.TreeMMS


