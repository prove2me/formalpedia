-- Prove2me | Definitions.Def_LocalPush_Supplement_Spectral
-- name    : LocalPush_Supplement_Spectral
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:18:22.002723+00:00
-- url     : https://prove2.me/theorems/c7351c03-ca67-4fd8-bff7-f9242efb6e84
-- title:
--   Laplacian $L=D-A$, effective resistance $R(s,t)$, spectral gap $\nu_2(G)$, edge count $m$, internal volume $\widetilde{\mathrm{vol}}(S)$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with degree vector $d$, degree matrix $D$ and adjacency matrix $A$.
--
--   1. The **Laplacian** is $L=D-A$.
--   2. The **effective resistance** between nodes $s,t$ is
--   $$R(s,t)=(e_s-e_t)^\top L^{+}(e_s-e_t),$$
--   where $L^{+}$ is the Moore–Penrose pseudoinverse of $L$.
--   3. The **spectral gap** $\nu_2(G)=\nu_2(D^{-1/2}LD^{-1/2})$, the second-smallest eigenvalue of the normalized Laplacian, given by its variational form
--   $$\nu_2(G)=\min_{g\ne0,\ d^\top g=0}\frac{g^\top Lg}{g^\top Dg}.$$
--   4. $m=|E|$ is the number of edges.
--   5. The **internal volume** of $S\subseteq V$ is $\widetilde{\mathrm{vol}}(S)=|S|+\big|\{\{u,v\}\in E:u,v\in S\}\big|$, as opposed to the volume $\mathrm{vol}(S)=\sum_{v\in S}d(v)$.
--
--   These are the quantities in the statements of Theorems 5.11, 6.1, 6.3, 7.1 and 7.4.
--
--   **Formalization Note** $L^{+}$ is the published operator pseudoinverse (`HarmonicGames.Decomposition.pinv`) of $x\mapsto Lx$ on Euclidean $\mathbb R^V$, which is the matrix Moore–Penrose pseudoinverse. $\nu_2$ is defined as an infimum over $\{g\ne0: d^\top g=0\}$; on graphs without isolated nodes and with at least two nodes this set is nonempty and the quotient is bounded below by $0$, so the infimum is the true minimum, which p.15 states equals the second-smallest eigenvalue.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §4 "Spectral gap" and "Effective resistance and electric flow", p.15 (PDF p.15); internal volume, §5.3, p.27 (PDF p.27); m := |E|, §1.1, p.4

import Mathlib
import Definitions.Def_LocalPush_GraphMatrices
import Definitions.Def_HarmonicGames_Decomposition_Pinv

open Finset Matrix

namespace LocalPush

namespace Supplement

/-!
# Laplacian, effective resistance, spectral gap, edge count and internal volume

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…): §4 "Spectral gap" and
"Effective resistance and electric flow", p.15 (PDF p.15); the internal volume, §5.3, p.27 (PDF p.27);
`m := |E|`, §1.1, p.4.

* `L := D − A` (unit weights).
* `R(s, t) := (e_s − e_t)ᵀ L⁺ (e_s − e_t)`, with `L⁺` the Moore–Penrose pseudoinverse.
* `ν₂(G) := ν₂(D^{−1/2} L D^{−1/2})`, in its variational form (p.15):
  `ν₂(G) = min_{g ≠ 0, dᵀg = 0} gᵀLg / gᵀDg`.
* `vol~(S) := |S| + |{{u, v} ∈ E : u, v ∈ S}|`.

**Formalization Note.**
* `L⁺` is the published operator pseudoinverse `HarmonicGames.Decomposition.pinv` of the linear map
  `x ↦ Lx` of Euclidean space `ℝ^V` (standard inner product), which is the matrix Moore–Penrose pseudoinverse.
* `ν₂` is defined by the variational characterization that p.15 states as equal to the second-smallest
  eigenvalue of the normalized Laplacian. It is an infimum of real numbers: on a graph without isolated nodes
  and with at least two nodes the set is nonempty (some `g ≠ 0` is orthogonal to `d`) and bounded below by
  `0` (`L` is positive semidefinite), so the infimum is the true minimum. Every statement using `ν₂` has
  two distinct nodes and no isolated nodes.
* `numEdges G = |E|` is the paper's `m`. `volInt G S` is `vol~(S)`; it differs from the base `vol` (sum of
  degrees).
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph Laplacian `L := D − A`. -/
def lap (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  degM G - adjM G

/-- The effective resistance `R(s, t) := (e_s − e_t)ᵀ L⁺ (e_s − e_t)` (p.15). -/
noncomputable def effRes (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) : ℝ :=
  (e s - e t) ⬝ᵥ
    (HarmonicGames.Decomposition.pinv (Matrix.toEuclideanLin (lap G)) (WithLp.toLp 2 (e s - e t))).ofLp

/-- The spectral gap `ν₂(G)`, the second-smallest eigenvalue of `D^{−1/2} L D^{−1/2}`, in the variational
form `inf {gᵀLg / gᵀDg : g ≠ 0, dᵀg = 0}` of p.15. -/
noncomputable def nu2 (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sInf {q : ℝ | ∃ g : V → ℝ, g ≠ 0 ∧ deg G ⬝ᵥ g = 0 ∧
    q = (g ⬝ᵥ (lap G *ᵥ g)) / (g ⬝ᵥ (degM G *ᵥ g))}

/-- The number of edges `m = |E|`. -/
def numEdges (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

open scoped Classical in
/-- The internal volume `vol~(S) := |S| + |{{u, v} ∈ E : u, v ∈ S}|` (p.27). -/
noncomputable def volInt (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  (S.card : ℝ) + ((G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ S).card : ℝ)

end Supplement

end LocalPush


