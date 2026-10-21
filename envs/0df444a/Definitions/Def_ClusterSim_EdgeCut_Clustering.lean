-- Prove2me | Definitions.Def_ClusterSim_EdgeCut_Clustering
-- name    : ClusterSim_EdgeCut_Clustering
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:50.67481+00:00
-- url     : https://prove2.me/theorems/1f4f4104-bba7-4000-9d62-d64774c32ff0
-- title:
--   Clusterings S_1, …, S_r of a tensor network, the cut edges E_cut, the qubit count d(S_i), (K, d)-clustered networks and the induced clustering of (G′, A_s) (pp. 2–3, 9–10)
-- statement:
--   Let $(G,\mathcal A)$ be a tensor network.
--
--   1. **Clustering.** A clustering into $r$ clusters consists of a distinguished vertex $O_f$, the final observable, which has no outgoing edge, and a label in $\{1,\dots,r\}$ for every other vertex; the clusters $S_1,\dots,S_r$ are the label classes ("setting the final observable $O_f$ aside, we partition the remaining vertices of $G$ into clusters $S_1,\dots,S_r$", p. 2).
--   2. **Cut edges.** $E_{\mathrm{cut}}$ is the set of edges that connect different clusters; the edges into $O_f$ are not included (proof of Theorem 1, p. 9, and footnote [63]).
--   3. **Qubits of a cluster.** $d(S_i)$ is the number of $\triangleleft$ vertices of $S_i$ (vertices without an incoming edge) plus the number of edges that enter $S_i$ from another cluster (p. 3).
--   4. **$(K,d)$-clustered.** The clustering is $(K,d)$-clustered if $|E_{\mathrm{cut}}|=K$ and $d(S_i)\le d$ for every $i$, i.e. $d$ bounds the paper's estimate $\max_i d(S_i)$ of the number of qubits sufficient for simulating each cluster.
--   5. **Induced clustering of a cut network.** If every edge of $E_{\mathrm{cut}}$ is cut (with any $s\in[8]^{E_{\mathrm{cut}}}$), the cut network $(G',\mathcal A_s)$ inherits a clustering: $O_f$ stays the final observable, each original vertex keeps its cluster, the new observable vertex $\triangleright_e$ joins the cluster of the source of $e$ and the new state vertex $\triangleleft_e$ the cluster of its target.
--
--   These notions turn the paper's informal "$(K,d)$-clustered circuit consisting of $r$ clusters" into a statement about a tensor network, and item 5 describes the $r$ pieces into which every cut network falls.
--
--   **Formalization Note** Cluster labels are `Fin r`; the label of $O_f$ is a junk value that no definition reads. Clusters may be empty. The paper defines $d(S_i)$ as the out-degree of $S_i$ (p. 2) and equates it with "the number of $\triangleleft$ vertices in $S_i$ plus the number of incoming edges to $S_i$" (p. 3); the formalization uses the second form, which is the one that upper-bounds the qubits a cluster needs. A $\triangleleft$ vertex is recognized by having no incoming edge. The structural fact that $O_f$ has no outgoing edge in the induced clustering is proved inside the definition.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, pp. 2–3, Clustered circuits; p. 9, proof of Theorem 1; p. 7, footnote [63]; p. 10, proof of Theorem 1

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_Cut

namespace ClusterSim.EdgeCut

noncomputable section

/-- A clustering of a tensor network into `r` clusters (Letter, "Clustered circuits", pp. 2–3):
a distinguished final observable vertex `obs` (the paper's `O_f`), which has no outgoing edge
("▷ vertices only have incoming edges", p. 2), and a cluster label `cl v ∈ Fin r` for every other
vertex (the clusters `S_1, …, S_r`; the label of `obs` itself is never used). -/
structure Clustering (G : TensorNetwork) (r : ℕ) where
  /-- the final observable `O_f` -/
  obs : G.V
  /-- the cluster of each vertex other than `O_f` -/
  cl : G.V → Fin r
  /-- `O_f` has no outgoing edge -/
  obs_no_out : ∀ e, G.src e ≠ obs

namespace Clustering

variable {G : TensorNetwork} {r : ℕ} (P : Clustering G r)

/-- `E_cut`, the edges that connect different clusters (proof of Theorem 1, p. 9); edges into
`O_f` are not included (footnote [63], p. 7). -/
def Ecut : Finset G.E :=
  Finset.univ.filter fun e => G.tgt e ≠ P.obs ∧ P.cl (G.src e) ≠ P.cl (G.tgt e)

/-- `d(S_i)`, the number of qubits needed for cluster `i` (pp. 2–3): the number of `◁` vertices
(vertices with no incoming edge) in `S_i` plus the number of edges entering `S_i` from another
cluster (edges into `O_f` excluded). -/
def qubits (i : Fin r) : ℕ :=
  (Finset.univ.filter fun v => v ≠ P.obs ∧ P.cl v = i ∧ ∀ e, G.tgt e ≠ v).card +
  (Finset.univ.filter fun e => G.tgt e ≠ P.obs ∧ P.cl (G.tgt e) = i ∧ P.cl (G.src e) ≠ i).card

/-- `(K, d)`-clustered (pp. 2–3, p. 9): exactly `K` edges connect different clusters
(`|E_cut| = K`), and every cluster needs at most `d` qubits (`max_i d(S_i) ≤ d`). -/
def IsClustered (K d : ℕ) : Prop :=
  P.Ecut.card = K ∧ ∀ i, P.qubits i ≤ d

/-- The clustering of the cut network `(G′, A_s)` obtained by cutting every edge of `E_cut`:
`O_f` stays the final observable, original vertices keep their cluster, the new observable
vertex `▷_e` joins the cluster of `src e` and the new state vertex `◁_e` the cluster of
`tgt e` (proof of Lemma 1, p. 9, and of Theorem 1, p. 10). -/
def cutClustering (s : P.Ecut → Fin 8) : Clustering (cut G P.Ecut s) r where
  obs := Sum.inl P.obs
  cl
    | Sum.inl v => P.cl v
    | Sum.inr (Sum.inl e) => P.cl (G.src e.1)
    | Sum.inr (Sum.inr e) => P.cl (G.tgt e.1)
  obs_no_out := by
    rintro (e | e) <;> simp [cut, P.obs_no_out]

end Clustering

end

end ClusterSim.EdgeCut


