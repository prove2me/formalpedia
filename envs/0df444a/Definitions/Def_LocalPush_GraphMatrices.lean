-- Prove2me | Definitions.Def_LocalPush_GraphMatrices
-- name    : LocalPush_GraphMatrices
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:03:38.382774+00:00
-- url     : https://prove2.me/theorems/d479c3ee-09ee-431b-bd52-6a5b45f95d46
-- title:
--   Degrees, adjacency matrix $A$, $D$, $L_\alpha=D-(1-\alpha)A$, volume, support, external boundary $\partial S$
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph. The paper assumes throughout that $G$ has no isolated nodes; this is the predicate `NoIsolated`. Write $d(v)$ for the degree of $v$, $A$ for the adjacency matrix, $D=\operatorname{diag}(d)$, and for a teleportation parameter $\alpha$
--   $$L_\alpha := D-(1-\alpha)A.$$
--   For $S\subseteq V$ the volume is $\mathrm{vol}(S)=\sum_{v\in S}d(v)$; for $x\in\mathbb R^V$ the support is $\mathrm{supp}(x)=\{v: x(v)\neq 0\}$; $e_s$ is the standard basis vector of $s$; and the external boundary of $S$ is
--   $$\partial S := \{v\in V\setminus S : N(v)\cap S\neq\emptyset\}.$$
--
--   These are the graph quantities in which PageRank, the residue map and the active-set algorithm are written.
--
--   **Formalization Note** `Dinv` is the diagonal matrix of reciprocal degrees, which is $D^{-1}$ because every degree is positive under `NoIsolated`. Disconnected graphs are allowed.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §1.1, p.4 (PDF p.4); §4, p.14 (PDF p.14)

import Mathlib

open Finset Matrix

namespace LocalPush

/-!
# Graph matrices: degrees, adjacency, `D`, `L_α`, volume, support, external boundary

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §1.1, p.4 (PDF p.4), and §4,
p.14 (PDF p.14).

"Throughout, G = (V, E) denotes an unweighted, undirected simple graph on n := |V| nodes with m := |E| edges.
We assume that the graph contains no isolated nodes." The matrices are `A`, `D`, `L_α := D − (1 − α)A`,
`vol(S) := ∑_{v∈S} d(v)`, `supp(x) := {v : x(v) ≠ 0}` and the external boundary
`∂S := {v ∈ V ∖ S : N(v) ∩ S ≠ ∅}`.

**Formalization Note.**
* The graph is a Mathlib `SimpleGraph` on a finite vertex type `V`; disconnected graphs are allowed, as on p.4.
  The standing assumption "no isolated nodes" is the separate predicate `NoIsolated`, a hypothesis of every
  statement that uses it.
* `Dinv` is the diagonal matrix of reciprocal degrees. It is the inverse `D⁻¹` of the paper exactly when every
  degree is positive (`NoIsolated`), which every statement of the mission assumes.
* `e s` is the standard basis vector `e_s`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The standing assumption of §1.1, p.4: the graph contains no isolated nodes. -/
def NoIsolated (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, 0 < G.degree v

/-- The degree `d(v)` as a real number (the degree vector `d`). -/
def deg (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℝ :=
  (G.degree v : ℝ)

/-- The adjacency matrix `A`. -/
def adjM (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  G.adjMatrix ℝ

/-- The diagonal degree matrix `D`. -/
def degM (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.diagonal (deg G)

/-- The diagonal matrix of reciprocal degrees, `D⁻¹` when every degree is positive. -/
noncomputable def Dinv (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.diagonal fun v => (deg G v)⁻¹

/-- `L_α := D − (1 − α)A` (§4, p.14). -/
def Lα (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) : Matrix V V ℝ :=
  degM G - (1 - α) • adjM G

/-- The volume `vol(S) := ∑_{v∈S} d(v)`. -/
def vol (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  ∑ v ∈ S, deg G v

open scoped Classical in
/-- The support `supp(x) := {v : x(v) ≠ 0}`. -/
noncomputable def supp (x : V → ℝ) : Finset V :=
  univ.filter fun v => x v ≠ 0

/-- The standard basis vector `e_s`. -/
def e (s : V) : V → ℝ :=
  Pi.single s 1

/-- The external boundary `∂S := {v ∈ V ∖ S : N(v) ∩ S ≠ ∅}` (§4, p.14). -/
def bdry (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  univ.filter fun v => v ∉ S ∧ ∃ u ∈ S, G.Adj v u

end LocalPush


