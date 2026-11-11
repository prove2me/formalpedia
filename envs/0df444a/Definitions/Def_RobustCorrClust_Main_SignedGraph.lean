-- Prove2me | Definitions.Def_RobustCorrClust_Main_SignedGraph
-- name    : RobustCorrClust_Main_SignedGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:38:51.956847+00:00
-- url     : https://prove2.me/theorems/3951403b-be93-4484-b167-603ea4670f98
-- title:
--   Signed complete graphs, clusterings, cost and OPT, the encodings A and O^C, the square loss Ψ_G (§3.1, §4.1)
-- statement:
--   A **complete signed graph** on the vertex set $V=\{0,\dots,n-1\}$ is given by the simple graph $G$ of its **positive** pairs $E^+$; every other unordered pair of distinct vertices is **negative** ($E^-$). A **clustering** $\mathcal C$ is a partition of $V$, given by its same-cluster equivalence relation.
--
--   - $\mathrm{cost}_G(\mathcal C)$ is the number of unordered pairs $\{u,v\}$, $u\ne v$, that are positive and split by $\mathcal C$ or negative and joined by $\mathcal C$ (the published `CorrClustBBC.Cautious.mistakes`).
--   - $\mathrm{OPT}(G)=\min_{\mathcal C}\mathrm{cost}_G(\mathcal C)$; $\mathcal C^*$ is **optimal** if $\mathrm{cost}_G(\mathcal C^*)\le\mathrm{cost}_G(\mathcal D)$ for every clustering $\mathcal D$. $m=|E^+|$.
--   - The adjacency matrix $A$: $A_{uv}=1$ if $\{u,v\}\in E^+$ and $0$ otherwise (zero diagonal). The cluster matrix $O^{\mathcal C}$: $O^{\mathcal C}_{uv}=1$ if $u,v$ are in the same cluster (so $O^{\mathcal C}_{uu}=1$), else $0$.
--   - For a real $n\times n$ matrix $Y$, the **square loss** is
--   $$\Psi_G(Y)=\sum_{u<v}(Y_{uv}-A_{uv})^2,$$
--   the sum over unordered pairs of distinct vertices, each once.
--   - $|E^+_G\triangle E^+_Q|$ is the number of unordered pairs positive in exactly one of two signed graphs $G,Q$ on the same vertex set.
--
--   **Formalization Note.** Vertices are `Fin n`; a clustering is a `Setoid (Fin n)`; `OPT` is `sInf` of the (nonempty) set of costs, which is attained.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 11, §3.1; p. 16, §4.1; p. 44, Lemma 6.2

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace RobustCorrClust.Main

open Finset Classical

/-! Cao, Fabius, Wang, *Efficient Correlation Clustering in Single-pass Graph Streams:
Deterministic and Adversarially Robust*, STOC 2027 submission, §3.1 (p. 11) and §4.1 (p. 16).

A complete signed graph on the vertex set `V = Fin n` is encoded by the simple graph `G` of its
positive pairs `E⁺`; every other unordered pair of distinct vertices is negative (`E⁻`).
A clustering is a partition of `V`, encoded as a `Setoid (Fin n)` (its same-cluster relation). -/

/-- `cost_G(C)`: the number of unordered pairs `{u, v}`, `u ≠ v`, that are positive and split by
`C` or negative and joined by `C` (p. 11). This is the published
`CorrClustBBC.Cautious.mistakes`, applied to the same-cluster relation of `C`. -/
noncomputable def cost {n : ℕ} (G : SimpleGraph (Fin n)) (C : Setoid (Fin n)) : ℕ :=
  CorrClustBBC.Cautious.mistakes G C.r

/-- `OPT(G)`: the least cost of a clustering of `G` (p. 11). The set of costs is a nonempty set of
natural numbers (the discrete partition is a clustering), so the infimum is attained. -/
noncomputable def OPT {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf (Set.range (cost G))

/-- `C` is an optimal clustering of `G`: no clustering has smaller cost. -/
def IsOptimal {n : ℕ} (G : SimpleGraph (Fin n)) (C : Setoid (Fin n)) : Prop :=
  ∀ D : Setoid (Fin n), cost G C ≤ cost G D

/-- `m = |E⁺|`, the number of positive pairs. -/
noncomputable def numPos {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  G.edgeFinset.card

/-- The adjacency matrix `A` of the positive graph (§4.1, p. 16): `A_uv = 1` if `{u, v} ∈ E⁺`,
else `0`; in particular the diagonal is `0`. -/
noncomputable def adjMat {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun u v => if G.Adj u v then 1 else 0

/-- The matrix encoding `O^C` of a clustering (§4.1, p. 16): `O^C_uv = 1` if `u, v` lie in the
same cluster (so `O^C_uu = 1`), else `0`. -/
noncomputable def clusterMat {n : ℕ} (C : Setoid (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun u v => if C.r u v then 1 else 0

/-- `∑_{u<v} F u v`: the sum over unordered pairs of distinct vertices, each once. -/
noncomputable def pairSum {n : ℕ} (F : Fin n → Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, if u < v then F u v else 0

/-- The square loss `Ψ_G(Y) = ∑_{u<v} (Y_uv − A_uv)²` (§4.1, p. 16, and eq. (2), p. 6). -/
noncomputable def PsiG {n : ℕ} (G : SimpleGraph (Fin n)) (Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  pairSum (fun u v => (Y u v - adjMat G u v) ^ 2)

/-- `|E⁺_G △ E⁺_Q|`: the number of unordered pairs that are positive in exactly one of `G`, `Q`
(Lemma 6.2, p. 44). -/
noncomputable def symmDiffCount {n : ℕ} (G Q : SimpleGraph (Fin n)) : ℕ :=
  (symmDiff G.edgeFinset Q.edgeFinset).card

end RobustCorrClust.Main


