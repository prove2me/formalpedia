-- Prove2me | Definitions.Def_PhaseEncodedQGE_GraphNbhd
-- name    : PhaseEncodedQGE_GraphNbhd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:46:56.312587+00:00
-- url     : https://prove2.me/theorems/b4a79624-bb60-4af0-bd71-2400b8376f6c
-- title:
--   Neighbourhoods, degrees, cubic graphs, defect neighbour counts $k_j(D)$ and spin sums $S_i(x)$
-- statement:
--   Let $G$ be a simple graph on the vertex set $\{0,\dots,n-1\}$.
--
--   1. $N(j)$ is the set of neighbours of $j$, $d_v=|N(v)|$ is the degree of $v$, and $d_{\max}=\max_v d_v$ (taken to be $0$ when $n=0$).
--   2. $G$ is **cubic** when $d_v=3$ for every vertex $v$.
--   3. For a vertex $j$ and a set $D$ of vertices, $k_j(D)=|N(j)\cap D|$ is the number of neighbours of $j$ in $D$.
--   4. For an outcome $x$ and a vertex $i$, the neighbour spin sum is
--   $$S_i(x)=\sum_{v\in N(i)} z_v .$$
--
--   On a cubic graph $S_i(x)=2k_i(D(x))-3$; the counts $k_j(D)$ are the local data from which the profiles, extremal counts and odd readings of the mission are built.
--
--   **Formalization Note** Adjacency is decided classically, so all notions are defined for an arbitrary `SimpleGraph (Fin n)`.
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §2, p.4 (PDF p.5), eq. (1); §2, p.5 (PDF p.6), above eq. (3); §3.1, p.6 (PDF p.7); App. A.1, p.13 (PDF p.14), eq. (17)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Outcome
set_option autoImplicit false

namespace PhaseEncodedQGE

open Classical in
/-- The neighbourhood `N(j)` of vertex `j` in a simple graph on the vertex set `{0, …, n−1}`
(Miller, Lee, STOC 2027 submission (build 2026-11-03), §2, p.4).

**Formalization Note** Decidability of adjacency is classical, so every notion of the mission is
defined for an arbitrary `SimpleGraph (Fin n)`. -/
noncomputable def nbrs {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => G.Adj j v)

/-- The degree `d_v = |N(v)|` (§2, p.4, eq. (1)). -/
noncomputable def degree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ := (nbrs G v).card

/-- The maximum degree `d_max = max_v d_v` (§2, p.4); it is `0` when `n = 0`. -/
noncomputable def maxDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := Finset.univ.sup (degree G)

/-- `G` is cubic: every vertex has exactly three neighbours (§2, p.5; §3, p.6). -/
def IsCubic {n : ℕ} (G : SimpleGraph (Fin n)) : Prop := ∀ v, degree G v = 3

/-- `k_j(D) = |N(j) ∩ D|`, the number of neighbours of `j` in the defect set `D` (§2, p.5;
eq. (17), p.13). -/
noncomputable def kdef {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) (j : Fin n) : ℕ :=
  (nbrs G j ∩ D).card

/-- The neighbour spin sum `S_i(x) = ∑_{v ∈ N(i)} z_v` (§3.1, p.6; eq. (17), p.13). -/
noncomputable def spinSum {n : ℕ} (G : SimpleGraph (Fin n)) (x : Outcome n) (i : Fin n) : ℤ :=
  ∑ v ∈ nbrs G i, spin x v

end PhaseEncodedQGE


