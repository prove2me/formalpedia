-- Prove2me | Definitions.Def_FairDivisionGraph_TreeMMS_MMS
-- name    : FairDivisionGraph_TreeMMS_MMS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:48.525509+00:00
-- url     : https://prove2.me/theorems/fcb6f210-adf9-4f0c-acfd-9cebcc3c02a9
-- title:
--   Connected maximin share as a finite maximum
-- statement:
--   For a utility function $u$ and a labelled partition $P$ into $k$ parts, the partition value is $\min_{j<k}u(P_j)$. For a graph $G$ and residual vertices $V$, the connected maximin share is
--   $$\operatorname{mms}(G,V,k,u)=\max_{P\text{ a connected }k\text{-partition of }V}\min_{j<k}u(P_j).$$
--   The definition enumerates the finite family of partitions and takes its finite maximum. The minimum for zero parts and the maximum of an empty family are explicitly totalized by zero. These conventions do not supply a partition witness: on the theorem's tree domain, nonemptiness follows from $1\le k\le |V|$.
--
--   An MMS allocation is a valid allocation giving each agent at least her connected maximin share on the entire original vertex set. The factor is exactly one. General validity continues to allow empty bundles and unassigned vertices.
-- source:
--   Bouveret, Cechlárová, Elkind, Igarashi and Peters (2017), Fair Division of a Graph, IJCAI-17, https://doi.org/10.24963/ijcai.2017/20, §2, displayed MMS definition, printed p. 136 (PDF p. 2)

import Definitions.Def_FairDivisionGraph_TreeMMS_Model

set_option autoImplicit false

noncomputable section

namespace FairDivisionGraph.TreeMMS

/-- Least part value. The artificial zero-player case is totalized by zero. -/
def partitionValue {m k : ℕ} (u : Fin m → ℝ) (P : Fin k → Finset (Fin m)) : ℝ := by
  classical
  let vals := Finset.univ.image (fun j => value u (P j))
  exact if h : vals.Nonempty then vals.min' h else 0

/-- The actual finite family of connected partitions, not a supplied optimum. -/
def partitions {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (k : ℕ) : Finset (Fin k → Finset (Fin m)) := by
  classical
  exact Finset.univ.filter (ConnectedPartition G V)

/-- Maximum of the finite family of least-part values. Zero when no partition exists.
For a tree with `1 ≤ k ≤ |V|`, the connected family is nonempty; this fact is not an input. -/
def mms {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (k : ℕ) (u : Fin m → ℝ) : ℝ := by
  classical
  let vals := (partitions G V k).image (partitionValue u)
  exact if h : vals.Nonempty then vals.max' h else 0

/-- The connected-partition MMS guarantee, with factor exactly one. -/
def IsMMS {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (π : Fin n → Finset (Fin m)) : Prop :=
  Valid G π ∧ ∀ i, mms G Finset.univ n (u i) ≤ value (u i) (π i)

end FairDivisionGraph.TreeMMS

/-
BEGIN IMPORTED DEPENDENCY SOURCE

MODULE: Model
SHA256: 296ea53e433168aed88ae50d3345cd5d66705c6f11d264712fdc401f7adc3ca0

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

END IMPORTED DEPENDENCY SOURCE
-/


